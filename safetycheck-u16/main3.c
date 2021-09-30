#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

extern uint64_t FUNCTION(uint16_t*);

int main()
{
  int i;
  uint16_t r1;
  uint16_t io[] = 
  {1,1,1,1,
   2,2,2,2,
   3,3,3,3,
   4,4,4,4};
  
  r1 = FUNCTION(io);
  
  printf("%d -- ",r1);
  for(i=0;i<16;i++)
  { printf("%d; ",io[i]); }
  printf("\n");
  
  return 0;
}
