#include "../mmio.h"
void exit(int);
#include <stdint.h>

char* strncpy(char* dst, const char* src, int n){
  for(int i = 0; i < n; i++)
    dst[i] = src[i];
  return dst;
}

void bad(){
  putchars("BAD\n");
  exit(1);
}

int f(char* s){
  char buf[16];
  strncpy(buf,s, 100);
}

int main(int argc, char** argv){
  int buf[7];
  int pbad = (intptr_t)&bad;
  buf[5] = pbad;

  f((char*)buf);
  exit(0);
}




/* void ps(char* s){ */
/*   char c = *s; */
/*   if(!c) return; */
/*   putchar(c); */
/*   ps(s+1); */
/* } */

/* void phexit(char c){ */
/*   if (c < 10) */
/*     putchar('0' + c); */
/*   else */
/*     putchar('A' + (c-10)); */
/* } */

/* void phex(unsigned char c){ */
/*   phexit(((c & 0xff) >> 4) & 0x0f); */
/*   phexit((c & 0x0f)); */
/* } */

/* void phexi(unsigned int i){ */
/*   putchar('0'); putchar('x'); */
/*   phex(i >> 24); */
/*   phex(i >> 16); */
/*   phex(i >>  8); */
/*   phex(i      ); */
/* } */

/* void pmem(char* p, int n){ */
/*   putchar('\n'); */
/*   for(int i = 0; i < n; i+=1){ */
/*     phex(p[i]); */
/*     putchar(' '); */
/*     if((i+1) % 8 == 0) */
/*       putchar('\n'); */
/*   } */
/* } */
