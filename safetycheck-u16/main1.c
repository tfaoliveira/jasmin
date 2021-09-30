#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

extern uint64_t FUNCTION();

int main()
{
  uint16_t r1, r2, r3;
  
  r1 = FUNCTION();
  
  printf("%d\n",r1);
  
  return 0;
}
