#include <stdio.h>
#include <omp.h>

int main()
{
  int runningOnGPU = 0;
  /* Test if GPU is available using OpenMP4.5 */
#pragma omp target map(from:runningOnGPU)
  {
    if (omp_is_initial_device() == 0)
      runningOnGPU = 1;
  }
  /* If still running on CPU, GPU must not be available */
  if (runningOnGPU)
    printf("### Able to use the GPU! ### \n");
  else
    printf("### Unable to use the GPU, using CPU! ###\n");

  return 0;
}
