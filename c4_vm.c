// c4Runner. 
// Solo il codice di lancio di un programma compilato in C4.


#include <stdio.h>
#include <stdlib.h>
#include <memory.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>
#define int long long

char *p, *lp, // current position in source code
     *data,   // data bss pointer
     *d0,
     *e_e, *e_le, 
     *e_sp, *e_bp;     // pos. code enrico

int *e, *le,  // current position in emitted code
    *id,      // currently parsed identifier
    *sym,     // symbol table (simple list of identifiers)
    tk,       // current token
    ival,     // current token value
    ty,       // current expression type
    loc,      // local variable offset
    line,     // current line number
    src,      // print source and assembly flag
    debug,    // print executed instructions
    fl,       
    tmpn, *ili;     //file su cui compilare e intero temporaneo x salvataggio
// tokens and classes (operators last and in precedence order)
enum {
  Num = 128, Fun, Sys, Glo, Loc, Id,
  Char, Else, Enum, If, Int, Return, Sizeof, While,
  Assign, Cond, Lor, Lan, Or, Xor, And, Eq, Ne, Lt, Gt, Le, Ge, Shl, Shr, Add, Sub, Mul, Div, Mod, Inc, Dec, Brak
};

// opcodes
enum { LEA, LST, LDA, LIM ,JMP ,JSR ,BZ  ,BNZ ,ENT ,ADJ ,LEV ,LI  ,LC  ,SI  ,SC  ,PSH ,
       OR  ,XOR ,AND ,EQ  ,NE  ,LT  ,GT  ,LE  ,GE  ,SHL ,SHR ,ADD ,SUB ,MUL ,DIV ,MOD ,
       OPEN,READ,WRTE,CHMD,CLOS,PRTF,MALC,FREE,MSET,MCMP,GETC,EXIT };

// types
enum { CHAR, INT, PTR };

// identifier offsets (since we can't create an ident struct)
enum { Tk, Hash, Name, Class, Type, Val, HClass, HType, HVal, Idsz };

int get4(int fd)
{ char b[4];
  read(fd, b, 4);
  return (unsigned char)b[0]
       | ((unsigned char)b[1] << 8)
       | ((unsigned char)b[2] << 16)
       | ((unsigned char)b[3] << 24);
}
int runC4(char* fname, int argc, char** argv, int debug)
{ int esize, dsize, ssize; 
  int stackSize, fd; 
  int *pc, *sp, *bp, a, cycle; // vm registers
  int i, *t; // temps
  char* compile;
  char* dest;
  char by[4];
  // rimosso uso di bc32 (non supportato da C4)

  //Rileggo un file precompilato e lo eseguo.  
  if ((fd = open(fname, 0)) < 0) { printf("could not open(%s) for exec\n", fname); return -1; }
  read(fd, by, 3); 
  if (by[0]!='c'|| by[1]!='4' || by[2]!=':') { printf("invalid bytecode [%c%c%c]\n", by[0],by[1],by[2]); return -1; };

  dsize = get4(fd);  //Dimensione dei dati 
  ssize = get4(fd);  //Dimensione symbol table 
  esize = get4(fd);  // numero word codice
  tmpn = get4(fd);
  pc = (int*)(tmpn); // indice word del main

  stackSize = 10*1024; // arbitrary size
  if (!(sym = malloc(ssize))) { printf("could not malloc(%d) symbol area\n", ssize+8); return -1; }  //sym = Symbol table 
  if (!(le = e = malloc(esize * sizeof(int)))) { printf("could not malloc(%d) text area\n", (int)(esize * sizeof(int)) + 8); return -1; } //text
  pc = le + (int)pc;
  if (!(d0 = data = malloc(dsize))) { printf("could not malloc(%d) data area\n", dsize+8); return -1; }   //data
  if (!(sp = malloc(stackSize))) { printf("could not malloc(%d) stack area\n", stackSize); return -1; }    //stack 
  memset(sym,  0, ssize);
  memset(e,    0, esize * sizeof(int));
  memset(data, 0, dsize);
  d0=data; le=e; 
  read(fd, (char*)d0, dsize);  
//printf("Read data: %04X\n", dsize);  
  read(fd, (char*)sym, ssize);  
//printf("Read sym:  %04X\n", ssize);  
//printf("Read code: %04X\n", esize);  
 
// lettura codice a 32 bit word-by-word
  for (i = 0; i < esize; ++i)
    le[i] = get4(fd);
  close(fd); 
  // setup stack
  bp = sp = (int *)((int)sp + stackSize);
  *--sp = EXIT; // call exit if main returns
  *--sp = PSH; t = sp;
  *--sp = argc;
  *--sp = (int)argv;
  *--sp = (int)t; 

  // run...
  cycle=0;
  while (1) 
  { i = *pc++; ++cycle;
    if (debug) {
      printf("%08X [a=%08X sp=%08X bp=%08X]> %.4s", (pc - bp), a, (int)sp, (int)bp, 
        &"LEA ,LST, LDA, LIM ,JMP ,JSR ,BZ  ,BNZ ,ENT ,ADJ ,LEV ,LI  ,LC  ,SI  ,SC  ,PSH ,"
         "OR  ,XOR ,AND ,EQ  ,NE  ,LT  ,GT  ,LE  ,GE  ,SHL ,SHR ,ADD ,SUB ,MUL ,DIV ,MOD ,"
         "OPEN,READ,WRTE,CHMD,CLOS,PRTF,MALC,FREE,MSET,MCMP,GETC,EXIT,"[i * 5]);
      if (i <= ADJ) printf(" %08X\n", (int)*pc); else printf("\n");
    }
    if      (i == LEA) a = (int)(bp + *pc++);                             // load local address
    else if (i == LDA) a = (int)(d0 + *pc++);                             // load data address
    else if (i == LST) a = (int)(sym + *pc++);                            // load symbol table
    else if (i == LIM) a = *pc++;                                         // load immediate
    else if (i == JMP) 
    { dest=(int)((char *)*pc) + (char*)le; 
      //printf("JMP, le: %08X + val %08X = %08X\n", (int)le, (int)((int *)*pc), dest); 
      pc = (int*)dest;                       // jump relative to le
      //printf("next adr: %08X\n", pc); 
    }
    else if (i == JSR) 
    { *--sp = (int)(pc + 1); 
      dest=(int)((char *)*pc) + (char*)le;
      pc = (int*)dest;
    }   // jump to subroutine relative to le
    else if (i == BZ) 
    { dest=(int)((char *)*pc) + (char*)le;
      pc = a ? pc + 1 : (int*)dest;                 // branch if zero relative to le
    }
    else if (i == BNZ) 
    { dest=(int)((char *)*pc) + (char*)le;
      pc = a ? (int*)dest : pc + 1;                 // branch if not zero relative to le
    } 
    else if (i == ENT) { *--sp = (int)bp; bp = sp; sp = sp - *pc++; }     // enter subroutine
    else if (i == ADJ) sp = sp + *pc++;                                   // stack adjust
    else if (i == LEV) { sp = bp; bp = (int *)*sp++; pc = (int *)*sp++; } // leave subroutine
    else if (i == LI)  a = *(int *)a;                                     // load int
    else if (i == LC)  a = *(char *)a;                                    // load char

    else if (i == SI)
    { *(int *)*sp++ = a;                                 // store int
    }
    else if (i == SC)  a = *(char *)*sp++ = a;                            // store char
    else if (i == PSH) *--sp = a;                                         // push

    else if (i == OR)  a = *sp++ |  a;
    else if (i == XOR) a = *sp++ ^  a;
    else if (i == AND) a = *sp++ &  a;
    else if (i == EQ)  a = *sp++ == a;
    else if (i == NE)  a = *sp++ != a;
    else if (i == LT)  a = *sp++ <  a;
    else if (i == GT)  a = *sp++ >  a;
    else if (i == LE)  a = *sp++ <= a;
    else if (i == GE)  a = *sp++ >= a;
    else if (i == SHL) a = *sp++ << a;
    else if (i == SHR) a = *sp++ >> a;
    else if (i == ADD) a = *sp++ +  a;
    else if (i == SUB) a = *sp++ -  a;
    else if (i == MUL) a = *sp++ *  a;
    else if (i == DIV) a = *sp++ /  a;
    else if (i == MOD) a = *sp++ %  a;

    else if (i == OPEN) 
    { a = open((char *)sp[1], *sp);
    }
    else if (i == READ) a = read(sp[2], (char *)sp[1], *sp);
    else if (i == WRTE) a = write(sp[2], (char *)sp[1], *sp);
    else if (i == CHMD) a = chmod((char *)sp[1], *sp);
    else if (i == CLOS) a = close(*sp);
    else if (i == PRTF) { t = sp + pc[1]; a = printf((char *)t[-1], t[-2], t[-3], t[-4], t[-5], t[-6]); }
    else if (i == MALC) a = (int)malloc(*sp);
    else if (i == FREE) free((void *)*sp);
    else if (i == MSET) a = (int)memset((char *)sp[2], sp[1], *sp);
    else if (i == MCMP) a = memcmp((char *)sp[2], (char *)sp[1], *sp);
    else if (i == GETC) a=getc_nb(); 
    else if (i == EXIT) { //printf("exit(%d) cycle = %d\n", *sp, cycle); 
                          return *sp; 
                        }
    else { printf("unknown instruction = %d! cycle = %d\n", i, cycle); return -1; }
  }
}

int main(int argc, char **argv)
{ int debug=0;
//printf("par %s", argv[1]); 
  if (argc>0 && (argv[1][0] == '-') && (argv[1][1] == 'd') && (argv[1][2] == 0)) { debug = 1; --argc; ++argv; }; 
//printf("loading %s", argv[1]); 
  if (argc > 1)
  { char* fname=argv[1];
    --argc; ++argv; 
    runC4(fname, argc, argv, debug);
  } else printf("Uso: c4e [-d] file.4 parametri\n"); 
};
