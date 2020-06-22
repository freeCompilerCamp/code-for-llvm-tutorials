mul_add.ll:mul_add.c
	clang -S -O3 -emit-llvm mul_add.c
tut1:tut1.cpp
	c++ -g tut1.cpp `llvm-config --cxxflags --ldflags --libs core BitWriter --system-libs` -lpthread -o tut1
check:tu1
	./tut1
clean:
	rm -rf tut1 *.ll *.bc
