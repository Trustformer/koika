#include "../mmio.h"
void exit(int);
#include <stdint.h>
#include <stddef.h>

static int* const UART_ADDR    = (int*)0x40000000;

#define KALLOC_BASE ((void*)0x10000000)
#define KALLOC_END  ((void*)0x20000000)
#define PGSIZE 4096
#define PGROUNDUP(x) (((x)+PGSIZE-1) & ~(PGSIZE-1))
#define PGROUNDDOWN(x) (((x)) & ~(PGSIZE-1))

struct run { struct run * next; };
struct kmem { struct run * freelist; } kmem;

void kfree(void* pa){
  struct run* r;
  if ((int)pa % PGSIZE != 0 || pa < KALLOC_BASE || pa >= KALLOC_END){
    //error
    return;
  }
  r = (struct run*)pa;
  r -> next = kmem.freelist;
  kmem.freelist = r;
}

void* kalloc(){
  struct run * r = kmem.freelist;
  if(r) kmem.freelist = r->next;
  return r;
}

void freerange(void* start, void* end){
  void* p = (void*)PGROUNDUP((int)start);
  while (p + PGSIZE <= end){
    kfree(p);
    p+=PGSIZE;
  }
}

void kinit(){
  freerange(KALLOC_BASE, KALLOC_END);
}

char* gets(char* buf, size_t n){
  char* p = buf;
  char c;
  do {
    n--;
    c = getchar();
    putchar(c);
    if (c == '\r') {c = '\n';putchar('\n');}
    *p = c;
    p++;
  } while (c != '\n' && n > 0);
  *p = 0;
  return buf;
}

int strncmp(char* s1, char* s2, int n){
  for (int i = 0; i < n; i++){
    if (s1[i] < s2[i]) return -1;
    if (s1[i] > s2[i]) return 1;
    if (s1[i] == 0) return 0;
  }
  return 0;
}

int strcmp(char* s1, char* s2){
  while(*s1){
    if(!*s2) return 1;
    if (*s1 < *s2) return -1;
    if (*s1 > *s2) return 1;
    s1++; s2++;
  }
  if(!*s2) return 0;
  return -1;
}


#define MAXARG 10

void split(char *str, char **args, int *argc) {
  char recording = 0;
  while (*str && *argc < MAXARG) {
    if (*str == ' ') {
      if (recording) {
        *str = 0;
        str++;
        recording = 0;
        continue;
      }
    } else {
      if (!recording) {
        args[*argc] = str;
        *argc = *argc + 1;
        recording = 1;
      }
    }
    str++;
  }
}

/* void bov(){ */
/*   char s[1]; */
/*   strcpy(s, "AAAABBBBCCCCDDDD"); */
/* } */

/* void handle_command(char* cmd){ */
/*   char* args[MAXARG]; int argc = 0; */
/*   split(cmd, args, &argc); */
/*   if (!strcmp(args[0], "load")){ */
/*     putchars("Loading program '"); putchars(args[1]); putchars("'"); putln(); */
/*   } else if (!strcmp(args[0], "bov")){ */
/*     putchars("Doing bov!"); putln(); */
/*     bov(); */
/*   } else { */
/*     putchars("Invalid command '"); */
/*     putchars(cmd); */
/*     putchar('\''); */
/*     putln(); */
/*   } */
/* } */


void phexit(char c){
  if (c < 10)
    putchar('0' + c);
  else
    putchar('A' + (c-10));
}

void phex(unsigned char c){
  phexit(((c & 0xff) >> 4) & 0x0f);
  phexit((c & 0x0f));
}

void phexi(unsigned int i){
  putchar('0'); putchar('x');
  phex(i >> 24);
  phex(i >> 16);
  phex(i >>  8);
  phex(i      );
}

int getint(){
  int size = 0;
  size = size | (getchar() << 24);
  size = size | (getchar() << 16);
  size = size | (getchar() << 8);
  size = size | (getchar());
  return size;
}

//#define INTERACTIVE 1

int main(int argc, char** argv){
  char c;
  char buf[255];
  int i = 0;
  putchars("Hello"); putln();

  char data[] = {
    0x37, 0x21, 0x00, 0x00, 0x17, 0x05, 0x00, 0x00, 0x13, 0x05, 0x05, 0x04,
    0xef, 0x00, 0x00, 0x01, 0xb7, 0x15, 0x00, 0x40, 0x23, 0xa0, 0x05, 0x00,
    0x6f, 0x00, 0x00, 0x00, 0x93, 0x82, 0x00, 0x00, 0x13, 0x06, 0x05, 0x00,
    0xb7, 0x05, 0x00, 0x40, 0x03, 0x05, 0x06, 0x00, 0x63, 0x08, 0x05, 0x00,
    0x23, 0xa0, 0xa5, 0x00, 0x13, 0x06, 0x16, 0x00, 0x6f, 0xf0, 0x1f, 0xff,
    0x93, 0x80, 0x02, 0x00, 0x67, 0x80, 0x00, 0x00, 0x42, 0x6f, 0x6e, 0x6a,
    0x6f, 0x75, 0x72, 0x0d, 0x0a, 0x00, 0x00, 0x00
  };

  pause();
  int size =
#ifdef INTERACTIVE
    getint()
#else
    sizeof(data)
#endif
    ;
  putchars("size = "); phexi(size); putln();
  int entry =
#ifdef INTERACTIVE
    getint()
#else
    0
#endif
    ;
  putchars("entry = "); phexi(entry); putln();


  char* start_address = (char*)0xe00;
  char* p = start_address;
  for(int j = 0; j < size; j++){
    *(start_address + j) =
#ifdef INTERACTIVE
      getchar()
#else
      data[j]
#endif
    ;
  }

  for(int j = 0; j < size; j++){
    if (j % 16 == 0) {
      putln();
      phexi((int)(start_address + j));
      putchars("  ");
    } else if (j % 8 == 0) {
      putchar(' ');
    }
    phex(*(start_address + j));
    putchar(' ');
  }

  putln();


  putchars("Adresse de main: "); phexi((int)main); putln();

  putchars("Jumping to "); phexi((int)(start_address + entry)); putln();

  ((void(*)(void))(start_address + entry))();

  exit(0);
}

