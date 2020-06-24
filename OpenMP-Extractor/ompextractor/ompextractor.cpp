//===--------------------------ompextractor.cpp-----------------------------===
//
//
//Author: Gleison Souza Diniz Mendonca
//  [gleison.mendonca at dcc.ufmg.br | gleison14051994 at gmail.com]
//
//===-----------------------------------------------------------------------===
//
//OMP Extractor is a small plugin developed for the Clang C compiler front-end.
//Its goal is to provide auxiliary source-code information extracting information
//of Openmp pragmas, to permits people to understand and compare different openmp
//pragmas for the same benchamrk.
//
//More specifically, it collects information about the synctatical pragma
//constructions and pragmas that exist within a C/C++ source-code file. It then
//builds a Json file, which is a representation of those pragma blocks in the source
//file, where each loop is a node block with information about parallelization using
//OpenMP syntax.
//
//For each input file, its reference nodes are outputted as a JSON format file, that
//represents the loops inside the source code.
//
//Since it is a small self-contained plugin (not meant to be included by other
//applications), all the code is kept within its own source file, for simplici-
//ty's sake.
//
//By default, the plugin is built alongside an LLVM+Clang build, and its shared
//library file (ompextractor.so) can be found its build.
//
//The plugin can be set to run during any Clang compilation command, using the
//following syntax:
//
//  clang -Xclang -load -Xclang $SCOPE -Xclang -add-plugin -Xclang -extract-omp
//
//  Where $SCOPE -> points to the ompextractor.so shared library file location 
//===-----------------------------------------------------------------------===

#include "clang/Driver/Options.h"
#include "clang/AST/AST.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/Mangle.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/ASTConsumers.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include <stack>
#include <map>
#include <vector>
#include <fstream>

using namespace std;
using namespace clang;
using namespace llvm;

/*we can use this little baby to alter the original source code, if we ever feel
like it*/
Rewriter rewriter;

/*POD struct that represents a meaningful node in the AST, with its unique name
identifier and source location numbers*/
struct Node {
  string name;
  unsigned int id;
  unsigned int sline, scol;
  unsigned int eline, ecol;
};

typedef struct relative_loop_inst_id {
  string filename;
  string functionName;
  long long int functionLoopID;
  long long int loopInstructionID;
} relative_loop_inst_id;

/*POD struct that represents an input file in a Translation Unit (a single
source/header file). Each input file will have its own stack of traversable
nodes, and output file + associated information*/
struct InputFile {
	string filename;
	string labels;
	map<Stmt*, bool> visited;
	map<Stmt*, bool> isInsideTargetRegion;
	map<Stmt*, string> mapFunctionName;
	map<string, map<Stmt*, long long int> > functionLoopID;
	map<Stmt*, map<Stmt*, long long int> > loopInstructionID;
	map<Stmt*, relative_loop_inst_id> loopInstID;
	stack <struct Node> NodeStack;
};

/*we need a stack of active input files, to know which constructs belong to
which file*/
stack <struct InputFile> FileStack;

/*node counter, to uniquely identify nodes*/
long long int opCount = 0;

/*visitor class, inherits clang's ASTVisitor to traverse specific node types in
 the program's AST and retrieve useful information*/
class PragmaVisitor : public RecursiveASTVisitor<PragmaVisitor> {
private:
    ASTContext *astContext; //provides AST context info
    MangleContext *mangleContext;

public:
    explicit PragmaVisitor(CompilerInstance *CI) 
      : astContext(&(CI->getASTContext())) { // initialize private members
        rewriter.setSourceMgr(astContext->getSourceManager(),
        astContext->getLangOpts());
    }

    /*creates Node struct for a Stmt type or subtype
     *  used here just to provide information about loops (as "do", "while", "for").*/
    void CreateLoopNode(Stmt *st) {
        struct Node N;
        struct InputFile& currFile = FileStack.top();
	
        FullSourceLoc StartLocation = astContext->getFullLoc(st->getBeginLoc());
        FullSourceLoc EndLocation = astContext->getFullLoc(st->getEndLoc());
        if (!StartLocation.isValid() || !EndLocation.isValid() || (currFile.visited.count(st) != 0)) {
          N.sline = -1;
          return;
        }
	currFile.visited[st] = true;

        Stmt *body = nullptr;
        if (ForStmt *forst = dyn_cast<ForStmt>(st))
          body = forst->getBody();
        if (DoStmt *dost = dyn_cast<DoStmt>(st))
          body = dost->getBody();
        if (WhileStmt *whst = dyn_cast<WhileStmt>(st))
          body = whst->getBody();
        std:string snippet = getSourceSnippet(body->getSourceRange(), true, true);

        N.id = currFile.functionLoopID[currFile.mapFunctionName[st]][st];
        N.sline = StartLocation.getSpellingLineNumber();
        N.scol = StartLocation.getSpellingColumnNumber();
        N.eline = EndLocation.getSpellingLineNumber();
        N.ecol = EndLocation.getSpellingColumnNumber();
        N.name = st->getStmtClassName() + to_string(N.id);

	currFile.labels += "\"parallel loop " + to_string(opCount++) + "\":{\n";
        currFile.labels += "\"file\":\"" + currFile.filename + "\",\n";
	currFile.labels += "\"function\":\"" + currFile.mapFunctionName[st] + "\",\n";
	currFile.labels += "\"loop id\":\"" + to_string(N.id) + "\",\n";
        currFile.labels += "\"loop line\":\"" + to_string(N.sline) + "\",\n";
	currFile.labels += "\"loop column\":\"" + to_string(N.scol) + "\",\n";
	currFile.labels += "\"pragma type\":\"NULL\",\n";
	currFile.labels += "\"ordered\":\"false\",\n";
	currFile.labels += "\"offload\":\"false\",\n";
	currFile.labels += "\"multiversioned\":\"false\",\n";
	currFile.labels += "\"shared\":[],\n";
	currFile.labels += "\"private\":[],\n";
	currFile.labels += "\"firstprivate\":[],\n";
	currFile.labels += "\"lastprivate\":[],\n";
	currFile.labels += "\"linear\":[],\n";
	currFile.labels += "\"reduction\":[],\n";
	currFile.labels += "\"map to\":[],\n";
	currFile.labels += "\"map from\":[],\n";
	currFile.labels += "\"map tofrom\":[],\n";
	currFile.labels += "\"dependence list\":[],\n";
	currFile.labels += "\"body\":[" + snippet + "]\n";
	currFile.labels += "},\n";
    }

    /*classify each pragma depending of the directive used to create it*/
    string classifyPragma(OMPExecutableDirective *OMPLD, bool insideParallelRegion) {
      if (isa<OMPDistributeDirective>(OMPLD)) {
        return "distribute";
      }
      else if (isa<OMPDistributeParallelForDirective>(OMPLD)) {
        return "distribute parallel for";
      }
      else if (isa<OMPDistributeParallelForSimdDirective>(OMPLD)) {
        return "distribute parallel for smid";
      }
      else if (isa<OMPDistributeSimdDirective>(OMPLD)) {
        return "distribute simd";
      }
      else if (isa<OMPForDirective>(OMPLD)) {
	if (insideParallelRegion)
          return "parallel for";
        return "for";
      }
      else if (isa<OMPForSimdDirective>(OMPLD)) {
	if (insideParallelRegion)
          return "parallel for simd";
        return "for simd";
      }
      else if (isa<OMPParallelForDirective>(OMPLD)) {
        return "parallel for";
      }
      else if (isa<OMPParallelForSimdDirective>(OMPLD)) {
        return "parallel for simd";
      }
      else if (isa<OMPSimdDirective>(OMPLD)) {
        return "simd";
      }
      else if (isa<OMPTargetParallelForDirective>(OMPLD)) {
        return "target parallel for";
      }
      else if (isa<OMPTargetParallelForSimdDirective>(OMPLD)) {
        return "target parallel for simd";
      }
      else if (isa<OMPTargetSimdDirective>(OMPLD)) {
        return "target simd";
      }
      else if (isa<OMPTargetTeamsDistributeDirective>(OMPLD)) {
        return "target teams ditribute";
      }
      else if (isa<OMPTargetTeamsDistributeParallelForDirective>(OMPLD)) {
        return "target teams distribute parallel for";
      }
      else if (isa<OMPTargetTeamsDistributeParallelForSimdDirective>(OMPLD)) {
        return "target teams ditribute parallel for simd";
      }
      else if (isa<OMPTargetTeamsDistributeSimdDirective>(OMPLD)) {
        return "target teams ditribute simd";
      }
      else if (isa<OMPTaskLoopDirective>(OMPLD)) {
        return "taskloop";
      }
      else if (isa<OMPTaskLoopSimdDirective>(OMPLD)) {
        return "taskloop simd";
      }
      else if (isa<OMPTeamsDistributeDirective>(OMPLD)) {
        return "teams ditribute";
      }
      else if (isa<OMPTeamsDistributeParallelForDirective>(OMPLD)) {
        return "teams ditribute parallel for";
      }
      else if (isa<OMPTeamsDistributeParallelForSimdDirective>(OMPLD)) {
        return "teams ditribute parallel for simd";
      }
      else if (isa<OMPTeamsDistributeSimdDirective>(OMPLD)) {
        return "teams ditribute simd";
      }
      else if (isa<OMPTargetDataDirective>(OMPLD)) {
        return "target data";
      }
      return string();
    }

    /*each target directive needs to be identified as it creates a target region */ 
    bool isTargetDirective(OMPExecutableDirective *OMPLD) {
      if (isa<OMPTargetParallelForDirective>(OMPLD) ||
          isa<OMPTargetParallelForSimdDirective>(OMPLD) ||
          isa<OMPTargetTeamsDistributeDirective>(OMPLD) ||
          isa<OMPTargetTeamsDistributeParallelForDirective>(OMPLD) ||
          isa<OMPTargetTeamsDistributeParallelForSimdDirective>(OMPLD) ||
          isa<OMPTargetTeamsDistributeSimdDirective>(OMPLD) ||
	  //isa<OMPTargetDataDirective>(OMPLD) ||
	  //isa<OMPTargetEnterDataDirective>(OMPLD) ||
	  //isa<OMPTargetExitDataDirective>(OMPLD) ||
	  isa<OMPTargetParallelDirective>(OMPLD) ||
	  isa<OMPTargetTeamsDirective>(OMPLD) ||
	  isa<OMPTargetUpdateDirective>(OMPLD) ||
	  isa<OMPTargetDirective>(OMPLD))
	return true;
      return false;
    }

    /*recover the string that represents a statment, if possible. Just available for a sub set of directives*/
    string getStrForStmt(Stmt *st) {
      if (!st) {
	return string();
      }
      if (DeclRefExpr *DRex = dyn_cast<DeclRefExpr>(st)) {
        return DRex->getFoundDecl()->getNameAsString();
      }
      if (IntegerLiteral *IL = dyn_cast<IntegerLiteral>(st)) {
        return to_string((int) IL->getValue().roundToDouble());
      }
      if (OMPArraySectionExpr *OMPcl = dyn_cast<OMPArraySectionExpr>(st)) {
       std::string offsets = getStrForStmt(OMPcl->getBase()->IgnoreCasts());
       offsets += "[" + getStrForStmt(OMPcl->getLowerBound()->IgnoreImpCasts()) + ":";
       offsets += getStrForStmt(OMPcl->getLength()->IgnoreImpCasts()) + "]";
       return offsets;
     }
     if (ArraySubscriptExpr *ASExp = dyn_cast<ArraySubscriptExpr>(st)) {
       std::string offsets = getStrForStmt(ASExp->getBase()->IgnoreImpCasts());
       offsets += "[" + getStrForStmt(ASExp->getIdx()->IgnoreImpCasts()) + "]";
       return offsets;
     }
     if (ConstantExpr *ConstExp = dyn_cast<ConstantExpr>(st)) {
       return getStrForStmt(ConstExp->getSubExpr());
     }
     if (UnaryOperator *Uop = dyn_cast<UnaryOperator>(st)) {
       return getStrForStmt(Uop->getSubExpr());
     }
     return string();
    }

    /*visit each node walking in the sub-ast and provide a list stored as "nodes_list"*/
    void visitNodes(Stmt *st, vector<Stmt*> & nodes_list) {
      if (!st)
	return;
      nodes_list.push_back(st);
      if (CapturedStmt *CPTSt = dyn_cast<CapturedStmt>(st)) {
        visitNodes(CPTSt->getCapturedStmt(), nodes_list);
	return;
      }
      for (auto I = st->child_begin(), IE = st->child_end(); I != IE; I++) {
       visitNodes((*I)->IgnoreContainers(true), nodes_list);
      }
    }

    /*remove from clauses list the target string*/
    void removeIfClauseContains(std::string clause_type, map<string, string> & clauses, std::string target) {
       if (clauses.count(clause_type)) {
         if (clauses[clause_type].find(target) != std::string::npos) {
	   if (clauses[clause_type][(clauses[clause_type].find(target) + target.size() + 1)] == ',')
             clauses[clause_type].erase(clauses[clause_type].find(target) - 1, target.size()+3);
	   else if(clauses[clause_type][(clauses[clause_type].find(target) - 2)] == ',')
	     clauses[clause_type].erase(clauses[clause_type].find(target) - 2, target.size()+3);
	   else
	     clauses[clause_type].erase(clauses[clause_type].find(target) - 1, target.size()+2);
	 }
       }
    }

    /*Recover and associate the operand with the variable name*/
    std::string recoverOperandsForClause(OMPClause *clause) {
      if (OMPReductionClause *OMPcl = dyn_cast<OMPReductionClause>(clause)) {
	std::string op = OMPcl->getNameInfo().getName().getAsString();
	if (op.size() > 8)
          op.erase(op.begin(), op.begin() + 8);
        return (op + ":");
      }
      return std::string();
    }

    /*rewrite the clause as a string using the list its expressions*/
    void recoverClause(OMPClause *clause, std::string clause_type, map<string, string> & clauses,
		       MutableArrayRef<Expr *>::iterator list_begin,  MutableArrayRef<Expr *>::iterator list_end) {
      clauses[clause_type] = std::string();
      std::string operands = recoverOperandsForClause(clause);

      for (MutableArrayRef<Expr *>::iterator I = list_begin, IE = list_end; I != IE; I++) {
        if (Stmt *Nmdc = dyn_cast<Stmt>(*I)) {
          clauses[clause_type] += "\"" + operands + getStrForStmt(Nmdc) + "\",";
	}
      }
      if (clauses[clause_type].size() > 0) {
        clauses[clause_type].erase(clauses[clause_type].end()-1, clauses[clause_type].end());
      }
    }

    /*find clauses's variable lists and classify them depending of the clause used
     * (for example "private","shared", etc)*/
    void ClassifyClause(OMPClause *clause, map<string, string> & clauseType) {
      if (clause->isImplicit())
	return;
 
      /*Final or If clauses are marked as multiversioned.*/
      if (isa<OMPIfClause>(clause) ||
          isa<OMPFinalClause>(clause)) {
        clauseType["multiversioned"] = "true";
	return;
      }

      /*Collapse clause*/
      if (OMPCollapseClause *OMPCc = dyn_cast<OMPCollapseClause>(clause)) {
        clauseType["collapse"] = getStrForStmt(OMPCc->getNumForLoops());
      }

      /*Ordered clause.*/
      if (OMPOrderedClause *OMPcl = dyn_cast<OMPOrderedClause>(clause)) {
        clauseType["ordered"] = "true";
      }
      
      /*provide the list of variables associated to the private clause.*/
      if (OMPPrivateClause *OMPcl = dyn_cast<OMPPrivateClause>(clause))
        recoverClause(clause, "private", clauseType, OMPcl->varlist_begin(), OMPcl->varlist_end());

      /*provide the list of variables associated to the shared clause.*/
      if (OMPSharedClause *OMPcl = dyn_cast<OMPSharedClause>(clause))
        recoverClause(clause, "shared", clauseType, OMPcl->varlist_begin(), OMPcl->varlist_end());

      /*provide the list of variables associated to the firstprivate clause.*/
      if (OMPFirstprivateClause *OMPcl = dyn_cast<OMPFirstprivateClause>(clause))
        recoverClause(clause, "firstprivate", clauseType, OMPcl->varlist_begin(), OMPcl->varlist_end());

      /*provide the list of variables associated to the lastprivate clause.*/
      if (OMPLastprivateClause *OMPcl = dyn_cast<OMPLastprivateClause>(clause))
        recoverClause(clause, "lastprivate", clauseType, OMPcl->varlist_begin(), OMPcl->varlist_end());

      /*provide the list of variables associated to the linear clause.*/
      if (OMPLinearClause *OMPcl = dyn_cast<OMPLinearClause>(clause))
        recoverClause(clause, "linear", clauseType, OMPcl->varlist_begin(), OMPcl->varlist_end());

      /*provide the list of variables associated to the reduction clause.*/
      if (OMPReductionClause *OMPcl = dyn_cast<OMPReductionClause>(clause)) 
      	recoverClause(clause, "reduction", clauseType, OMPcl->varlist_begin(), OMPcl->varlist_end());

      /*provide the list of variables associated to the map clause.*/
      if (OMPMapClause *OMPcl = dyn_cast<OMPMapClause>(clause)) {
	 std::string index = "map" + std::to_string(OMPcl->getMapType());
         recoverClause(clause, index, clauseType, OMPcl->varlist_begin(), OMPcl->varlist_end());
      }
    }

    /*creates Node struct for a OMPLoopDirective type or subtype*/
    void CreateLoopDirectiveNode(Stmt *stmt, map<string, string> clauseType) {
        struct Node N;
        struct InputFile& currFile = FileStack.top();

	Stmt *st = nullptr;
	if (OMPExecutableDirective *OMPLD = dyn_cast<OMPExecutableDirective>(stmt))
	  st = OMPLD->getInnermostCapturedStmt()->getCapturedStmt();
	else if (isa<DoStmt>(stmt) || isa<ForStmt>(stmt) || isa<WhileStmt>(stmt)) {
          if (ForStmt *fstmt = dyn_cast<ForStmt>(stmt)) {
	    std::string incVar = getStrForStmt(fstmt->getInc());
            removeIfClauseContains("private", clauseType, incVar);
	    removeIfClauseContains("firstprivate", clauseType, incVar);
	    removeIfClauseContains("lastprivate", clauseType, incVar);
	  }
   	  st = stmt;
	}
	else
	  return;

        FullSourceLoc StartLocation = astContext->getFullLoc(st->getBeginLoc());
        FullSourceLoc EndLocation = astContext->getFullLoc(st->getEndLoc());
        if (!StartLocation.isValid() || !EndLocation.isValid() || (currFile.visited.count(st) != 0)) {
          return;
        }
        
        currFile.visited[st] = true;

        Stmt *body = nullptr;
        if (ForStmt *forst = dyn_cast<ForStmt>(st))
          body = forst->getBody();
        if (DoStmt *dost = dyn_cast<DoStmt>(st))
          body = dost->getBody();
        if (WhileStmt *whst = dyn_cast<WhileStmt>(st))
          body = whst->getBody();
        std:string snippet = getSourceSnippet(body->getSourceRange(), true, true);

        N.id = currFile.functionLoopID[currFile.mapFunctionName[st]][st];
        N.sline = StartLocation.getSpellingLineNumber();
        N.scol = StartLocation.getSpellingColumnNumber();
        N.eline = EndLocation.getSpellingLineNumber();
        N.ecol = EndLocation.getSpellingColumnNumber();
        N.name = st->getStmtClassName() + to_string(N.id);

        if (OMPExecutableDirective *OMPED = dyn_cast<OMPExecutableDirective>(stmt))
          clauseType["pragma type"] = classifyPragma(OMPED, (clauseType.count("parallel") > 0) == true);

	currFile.labels += "\"parallel loop " + to_string(opCount++) + "\":{\n";
	currFile.labels += "\"file\":\"" + currFile.filename + "\",\n";
	currFile.labels += "\"function\":\"" + currFile.mapFunctionName[st] + "\",\n";
        currFile.labels += "\"loop id\":\"" + to_string(N.id) + "\",\n";
        currFile.labels += "\"loop line\":\"" + to_string(N.sline) + "\",\n";
	currFile.labels += "\"loop column\":\"" + to_string(N.scol) + "\",\n";

	currFile.labels += "\"pragma type\":\"" + clauseType["pragma type"] + "\",\n";
	
        currFile.labels += "\"ordered\":\"" + ((clauseType.count("ordered") > 0) ? (clauseType["ordered"]) : "false") + "\",\n";
        currFile.labels += "\"offload\":\"" + ((clauseType.count("offload") > 0) ? (clauseType["offload"]) : "false") + "\",\n";
	currFile.labels += "\"multiversioned\":\""+ ((clauseType.count("multiversioned") > 0) ? (clauseType["multiversioned"]) : "false") + "\",\n";

	currFile.labels += "\"shared\":[" + ((clauseType.count("shared") > 0) ? (clauseType["shared"]) : "") + "],\n";
	currFile.labels += "\"private\":[" + ((clauseType.count("private") > 0) ? (clauseType["private"]) : "") + "],\n";
	currFile.labels += "\"firstprivate\":[" + ((clauseType.count("firstprivate") > 0) ? (clauseType["firstprivate"]) : "") + "],\n";
	currFile.labels += "\"lastprivate\":[" + ((clauseType.count("lastprivate") > 0) ? (clauseType["lastprivate"]) : "") + "],\n";
        currFile.labels += "\"linear\":[" + ((clauseType.count("linear") > 0) ? (clauseType["linear"]) : "") + "],\n";
	currFile.labels += "\"reduction\":[" + ((clauseType.count("reduction") > 0) ? (clauseType["reduction"]) : "") + "],\n";
        currFile.labels += "\"map to\":[" + ((clauseType.count("map1") > 0) ? (clauseType["map1"]) : "") + "],\n";
        currFile.labels += "\"map from\":[" + ((clauseType.count("map2") > 0) ? (clauseType["map2"]) : "") + "],\n";
        currFile.labels += "\"map tofrom\":[" + ((clauseType.count("map3") > 0) ? (clauseType["map3"]) : "") + "],\n";
	currFile.labels += "\"dependence list\":[" + ((clauseType.count("dependence list") > 0) ? (clauseType["dependence list"]) : "") + "],\n";
	currFile.labels += "\"body\":[" + snippet + "]\n";
	currFile.labels += "},\n";
    }

    /*Initializes a new input file and pushes it to the top of the file stack*/
    void NewInputFile(string filename) {
      struct InputFile newfile;
      struct Node root;

      newfile.filename = filename;
      FileStack.push(newfile);

      root.id = ++opCount;
      root.name = filename;
      root.sline = 0;
      root.scol = 0;
      root.eline = ~0;
      root.ecol = ~0;

      /*create parent node for the new file's scope tree*/
      FileStack.top().NodeStack.push(root);
    }      

    /*Replace all  occurrences in the target string*/
    std::string replace_all(std::string str, std::string from, std::string to) {
      int pos = 0;
      while((pos = str.find(from, pos)) != std::string::npos) {
	str.replace(pos, from.length(), to);
	pos = pos + to.length();
      }
      return str;
    }

    /*Recover C code to insert in the Json Files*/
    std::string getSourceSnippet(SourceRange sourceRange, bool allTokens, bool jsonForm) {
      SourceLocation bLoc(sourceRange.getBegin());
      SourceLocation eLoc(sourceRange.getEnd());
	   
      const SourceManager& mng = astContext->getSourceManager();
      std::pair<FileID, unsigned> bLocInfo = mng.getDecomposedLoc(bLoc);
      std::pair<FileID, unsigned> eLocInfo = mng.getDecomposedLoc(eLoc);
      FileID FID = bLocInfo.first;
      unsigned bFileOffset = bLocInfo.second;
      unsigned eFileOffset = eLocInfo.second;
      unsigned length = eFileOffset - bFileOffset;

      bool Invalid = false;
      const char *BufStart = mng.getBufferData(FID, &Invalid).data();
      if (Invalid)
        return std::string();

      if (allTokens == true) {
	while (true) {
	  if (BufStart[(bFileOffset + length)] == ';')
            break;
	  if (BufStart[(bFileOffset + length)] == '}')
	    break;
          length++;
	}
      }
      length++;
      
      std::string snippet = StringRef(BufStart + bFileOffset, length).trim().str();
      snippet = replace_all(snippet, "\\", "\\\\");
      snippet = replace_all(snippet, "\"", "\\\"");

      if (jsonForm == true)
	snippet = "\"" + replace_all(snippet, "\n", "\",\n\"") + "\"";

      return snippet;
    }

    /*Use Abstract Handles to represent target information into the source code*/
    void insertStmtDirectives(Stmt *st, std::string directive, std::string snippet, map<string, string> & clauses) {
      struct InputFile& currFile = FileStack.top();
      
      FullSourceLoc StartLocation = astContext->getFullLoc(st->getBeginLoc());
      FullSourceLoc EndLocation = astContext->getFullLoc(st->getEndLoc());
      if (!StartLocation.isValid() || !EndLocation.isValid()) {
	return;
      }

      currFile.labels += "\"" + directive + " " + std::to_string(opCount++) + "\":{\n";
      currFile.labels += "\"pragma type\":\"" + directive + "\",\n";
      currFile.labels += "\"file\":\"" + currFile.loopInstID[st].filename + "\",\n";
      currFile.labels += "\"function\":\"" + currFile.loopInstID[st].functionName  + "\",\n";
      currFile.labels += "\"loop id\":\"" + to_string(currFile.loopInstID[st].functionLoopID) + "\",\n";
      currFile.labels += "\"statement id\":\"" + to_string(currFile.loopInstID[st].loopInstructionID) + "\",\n";

      currFile.labels += "\"snippet line\":\"" + to_string(StartLocation.getSpellingLineNumber()) + "\",\n";
      currFile.labels += "\"snippet column\":\"" + to_string(StartLocation.getSpellingColumnNumber()) + "\",\n";

      currFile.labels += "\"code snippet\":[" + snippet + "]\n";
      currFile.labels += "},\n";

      // Insert the dependence
      if (clauses.count("dependence list") == 0)
        clauses["dependence list"] = "\"" + (directive + " " + std::to_string((opCount - 1))) + "\"";
      else
        clauses["dependence list"] += ",\"" + (directive + " " + std::to_string((opCount - 1))) + "\"";
    }

    /*associate the information of some node in the AST to it's sub tree. Important to normalize
     * standart information on each loop.*/
    void associateEachLoopInside(OMPExecutableDirective *OMPED, map<string, string> & clauses) {
      struct InputFile& currFile = FileStack.top();
      vector<Stmt*> nodes_list;
      visitNodes(OMPED, nodes_list);

      if (currFile.visited.count(OMPED) != 0)
	return;
      currFile.visited[OMPED] = true;

      if (isTargetDirective(OMPED))
        clauses["offload"] = "true";

      if (isa<OMPParallelDirective>(OMPED)) 
        clauses["parallel"] = "true";

      if (isa<OMPOrderedDirective>(OMPED)) {
	const SourceManager& mng = astContext->getSourceManager();
	std::string snippet = getSourceSnippet(OMPED->getInnermostCapturedStmt()->getSourceRange(), true, true);
	insertStmtDirectives(OMPED, "ordered", snippet, clauses);
      }

      if (OMPAtomicDirective * OMPAD = dyn_cast<OMPAtomicDirective>(OMPED)) {
	std::string snippet = getSourceSnippet(OMPAD->getInnermostCapturedStmt()->getSourceRange(), true, true);
        if (OMPAD->getNumClauses() > 0) {
	  if (isa<OMPCaptureClause>(OMPED->getClause(0)))
            insertStmtDirectives(OMPAD, "atomic capture", snippet, clauses);
	  else if (isa<OMPWriteClause>(OMPED->getClause(0)))
            insertStmtDirectives(OMPAD, "atomic write", snippet, clauses);
	  else if (isa<OMPReadClause>(OMPED->getClause(0)))
            insertStmtDirectives(OMPAD, "atomic read", snippet, clauses);
	  else if (isa<OMPUpdateClause>(OMPED->getClause(0)))
            insertStmtDirectives(OMPAD, "atomic update", snippet, clauses);
	}
	else
	  insertStmtDirectives(OMPAD, "atomic", snippet, clauses);
      }

      clauses["pragma type"] = classifyPragma(OMPED, (clauses.count("parallel") > 0) == true);

      if (isa<OMPTargetDataDirective>(OMPED) ||
           isa<OMPTargetEnterDataDirective>(OMPED) ||
           isa<OMPTargetExitDataDirective>(OMPED))
	 clauses["offload"] = "false";

      for (int i = 0, ie = OMPED->getNumClauses(); i != ie; i++)
        ClassifyClause(OMPED->getClause(i), clauses);
    
      for (int i = 0, ie = nodes_list.size(); i != ie; i++) {
        if (OMPOrderedDirective *OMPOD = dyn_cast<OMPOrderedDirective>(nodes_list[i]))
	  associateEachLoopInside(OMPOD, clauses);
	if (OMPAtomicDirective *OMPAD = dyn_cast<OMPAtomicDirective>(nodes_list[i]))
	  associateEachLoopInside(OMPAD, clauses);
      }

      /*we need do associate clauses for:
       * - collapsed loops
       * - target directives
       * - parallel */
      if ((clauses.count("collapse") != 0) ||
          (clauses.count("offload") != 0) ||
	  (clauses.count("parallel") != 0) ||
	  (isa<OMPTargetDataDirective>(OMPED) ||
           isa<OMPTargetEnterDataDirective>(OMPED) ||
           isa<OMPTargetExitDataDirective>(OMPED))) {

	if (clauses.count("collapse") != 0)
          CreateLoopDirectiveNode(OMPED, clauses);

        for (int i = 0, ie = nodes_list.size(); i != ie; i++) {
	  if (currFile.visited.count(nodes_list[i]) != 0) 
	    continue;

          if (clauses.count("collapse") != 0) {
            if (isa<DoStmt>(nodes_list[i]) || isa<ForStmt>(nodes_list[i]) || isa<WhileStmt>(nodes_list[i])) {
              clauses["collapse"] = std::to_string(std::stoi(clauses["collapse"]) - 1);
	      CreateLoopDirectiveNode(nodes_list[i], clauses);
	      if (clauses["collapse"] == "1")
		break;      
	    }
	  }

	  if (OMPExecutableDirective *OMPEN = dyn_cast<OMPExecutableDirective>(nodes_list[i])) {
            if (OMPLoopDirective *OMPLD = dyn_cast<OMPLoopDirective>(OMPEN)) {
              associateEachLoopInside(OMPLD, clauses);
            }
	    else if (OMPTargetDataDirective *OMPTD = dyn_cast<OMPTargetDataDirective>(OMPEN)) {
              associateEachLoopInside(OMPED, clauses); 
	    }
	    else if (OMPParallelDirective *OMPPD = dyn_cast<OMPParallelDirective>(OMPEN)) {
              associateEachLoopInside(OMPPD, clauses);
            }
	    else if (OMPTargetDirective *OMPTD = dyn_cast<OMPTargetDirective>(OMPEN)) {
      	      associateEachLoopInside(OMPTD, clauses);
	    }
	  }
        }
      }

      if (OMPLoopDirective *OMPLD = dyn_cast<OMPLoopDirective>(OMPED)) {
        CreateLoopDirectiveNode(OMPLD, clauses);
      }
    }

    /*Populate a map with the defined lines, to do that, we consider everything inside a statment as
     * a vector of characters, then we define new ids whenever we find the token ";".
     * The goal is be able to recover relative positions to statments when necessary, for example,
     * instructions inside a loop */
    void recoverCodeSnippetsID(Stmt *st, map<Stmt*, long long int> & mapped_statments, long long int loopID) {
      string snippet = getSourceSnippet(st->getSourceRange(), true, false);
      // The separator ref vector have the following format:
      // <line, column>, where that is the position of the character ';' in the source code
      // and the position of the vector is the relative id;
      vector<pair<int, int> > separator_ref;
      int line = 0;
      int column = 0;
      for (int i = 0, ie = snippet.size(); i < ie; i++) {
	// Store the positions with the character ';'
        if (snippet[i] == ';')
	  separator_ref.push_back(make_pair(line, column));
	column++;
	if (snippet[i] == '\n') {
	  line++;
	  column = 0;
	}
      }

      if (snippet[(snippet.size() - 1)] != ';')
        separator_ref.push_back(make_pair(line, column));

      vector<Stmt*> nodes_list;
      visitNodes(st, nodes_list);
      for (int i = 0, ie = nodes_list.size(); i != ie; i++) {
        FullSourceLoc StartLocation = astContext->getFullLoc(nodes_list[i]->getBeginLoc());
        FullSourceLoc EndLocation = astContext->getFullLoc(nodes_list[i]->getEndLoc());
	if (!StartLocation.isValid() || !EndLocation.isValid()) 
	  continue;

	int line  = EndLocation.getSpellingLineNumber();
        int column = EndLocation.getSpellingColumnNumber();

	mapped_statments[nodes_list[i]] = -1;
	for (int j = 0, je = separator_ref.size(); j != je; j++) {
          if (separator_ref[i].first == line) {
            if (separator_ref[i].second >= column) {
              mapped_statments[nodes_list[i]] = j + 1;
	      break;
	    }
	  }
	  else if (separator_ref[i].first > line) {
            mapped_statments[nodes_list[i]] = j + 1;
	    break;
	  }
	}
	if (mapped_statments[nodes_list[i]] == -1)
	  mapped_statments[nodes_list[i]] = separator_ref.size();

	// Associate the statment with a relative position. Provides facilities to recover the relative position
	// after this process
	struct InputFile& currFile = FileStack.top();
	currFile.loopInstID[nodes_list[i]].filename = currFile.filename;
	string functionName = currFile.mapFunctionName[nodes_list[i]];
	currFile.loopInstID[nodes_list[i]].functionName = functionName;
	currFile.loopInstID[nodes_list[i]].functionLoopID = loopID;
        currFile.loopInstID[nodes_list[i]].loopInstructionID = mapped_statments[nodes_list[i]];
      }
    }

    /*visits all nodes of type decl*/
    virtual bool VisitDecl(Decl *D) {
	struct InputFile& currFile = FileStack.top();

	if (FunctionDecl *FD = dyn_cast<FunctionDecl>(D)) {
	  if (FD->doesThisDeclarationHaveABody()) {

	    const SourceManager& mng = astContext->getSourceManager();

            if (astContext->getSourceManager().isInSystemHeader(D->getBeginLoc())) {
              return true;
            }

            string filename = mng.getFilename(D->getBeginLoc());

            if (FileStack.empty() || FileStack.top().filename != filename) {
              NewInputFile(filename);
            }
            struct InputFile& currFile = FileStack.top();
	
	    vector<Stmt*> nodes_list;
            visitNodes(FD->getBody(), nodes_list);
	    string funcName = FD->getNameInfo().getName().getAsString();
	    map<int, Stmt*> loops;
	    for (int i = 0, ie = nodes_list.size(); i != ie; i++) {
              if (isa<DoStmt>(nodes_list[i]) || isa<ForStmt>(nodes_list[i]) || isa<WhileStmt>(nodes_list[i])) {
                FullSourceLoc StartLocation = astContext->getFullLoc(nodes_list[i]->getBeginLoc());
                FullSourceLoc EndLocation = astContext->getFullLoc(nodes_list[i]->getEndLoc());
	        if (!StartLocation.isValid() || !EndLocation.isValid()) 
		  continue;

	        int line  = StartLocation.getSpellingLineNumber();
                loops[line] = nodes_list[i];
	      }
              currFile.mapFunctionName[nodes_list[i]] = funcName;
	    }
	    
	    int id = 1;
	    for (map<int, Stmt*>::iterator I = loops.begin(), IE = loops.end(); I != IE; I++) {
              currFile.functionLoopID[funcName][I->second] = id++;

	      int idInst = 1;
	      Stmt *st = nullptr;
	      if (ForStmt *forst = dyn_cast<ForStmt>(I->second))
		st = forst->getBody();
	      if (DoStmt *dost = dyn_cast<DoStmt>(I->second))
		st = dost->getBody();
	      if (WhileStmt *whst = dyn_cast<WhileStmt>(I->second))
		st = whst->getBody();
		
	      recoverCodeSnippetsID(st, currFile.loopInstructionID[st], currFile.functionLoopID[funcName][I->second]);
	    }
	  }
	}	
      return true;
    }

    /*visits all nodes of type stmt*/
    virtual bool VisitStmt(Stmt *st) {
	const SourceManager& mng = astContext->getSourceManager();

        /*skip non-scope generating statements (returning true resumes AST
        traversal)*/
        if (!isa<OMPExecutableDirective>(st) && !isa<DoStmt>(st) 
		&& !isa<ForStmt>(st) && !isa<WhileStmt>(st)) {
          return true;
        }

	if (OMPExecutableDirective *OMPED = dyn_cast<OMPExecutableDirective>(st)) {
	  map<string, string> clauses;
          associateEachLoopInside(OMPED, clauses);
	}

	if (isa<DoStmt>(st) || isa<ForStmt>(st) || isa<WhileStmt>(st)) {
          CreateLoopNode(st);
	}

        return true;
    }
};

class PragmaASTConsumer : public ASTConsumer {
private:
    PragmaVisitor *visitor; // doesn't have to be private

public:
    /*override the constructor in order to pass CI*/
    explicit PragmaASTConsumer(CompilerInstance *CI)
        : visitor(new PragmaVisitor(CI)) // initialize the visitor
    { }

    /*empties node stack (in between different translation units)*/
    void EmptyStack() {
      while (!FileStack.empty()) {
        FileStack.pop();
      }
    }

    /*writes scope dot file as output*/
    bool writeJsonToFile() {
      struct InputFile& currFile = FileStack.top(); 
      ofstream outfile;

      /*make sure we have a valid filename (input file could be empty, etc.)*/
      if (currFile.filename.empty()) {
        return false;
      }

      outfile.open(currFile.filename + ".json");

      /*couldn't open output file (might be a permissions issue, etc.)*/
      if (!outfile.is_open()) {
        return false;
      }
	
      /*we need to remove the last ",\n" before write the json*/
      if (currFile.labels.size() >= 2)
      currFile.labels.erase(currFile.labels.end() - 2, currFile.labels.end());
      /*output graph in JSON notation*/
      outfile << "{\n";
      outfile << currFile.labels << "\n}";

      return true;
    }

    /*we override HandleTranslationUnit so it calls our visitor
    after parsing each entire input file*/
    virtual void HandleTranslationUnit(ASTContext &Context) {
        /*traverse the AST*/
        visitor->TraverseDecl(Context.getTranslationUnitDecl());

        /*write the output JSON file*/
        while (!FileStack.empty()) {
          if (writeJsonToFile()) {
            errs() << "Pragma info for file " << FileStack.top().filename;
            errs() << " written successfully!\n";
          }

          else {
            errs() << "Failed to write dot file for input file: ";
            errs() << FileStack.top().filename << "\n";
          }

          FileStack.pop();
        } 
    }
};

class PragmaPluginAction : public PluginASTAction {
protected:
    /*This gets called by Clang when it invokes our Plugin.
    Has to be unique pointer (this bit was a bitch to figure out*/
    unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, 
                                              StringRef file) {
        return make_unique<PragmaASTConsumer>(&CI);
    }

    /*leaving this here as a placeholder for now, we can implement a function
    here to evaluate and handle input arguments, if ever necessary*/
    bool ParseArgs(const CompilerInstance &CI, const vector<string> &args) {
        return true;
    }
};

/*register the plugin and its invocation command in the compilation pipeline*/
static FrontendPluginRegistry::Add<PragmaPluginAction> X
                                               ("-extract-omp", "OMP Extractor");
