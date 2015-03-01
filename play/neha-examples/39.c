//#include <assert.h>
int __BLAST_NONDET;
int MAXPATHLEN;
int unknown();


/*
 * "NetBSD_loop_int" from InvGen benchmark suite
 */


int main()
{
  /*
  Char *buf;
  Char *pattern;
  Char *bound;
  */
  int buf_off;
  int pattern_off;
  int bound_off;

  //  int A [MAXPATHLEN+1];
  //  int B [PATTERNLEN];

  /* glob3's local vars */
  int glob3_pathbuf_off;
  int glob3_pathend_off;
  int glob3_pathlim_off;
  int glob3_pattern_off;
  int glob3_dc;

  if(MAXPATHLEN > 0); else goto END;

  /*
  buf = A;
  pattern = B;
  */
  buf_off = 0;
  pattern_off = 0;

  /* bound = A + sizeof(A)/sizeof(*A) - 1; */
  bound_off = 0 + (MAXPATHLEN + 1) - 1;

  glob3_pathbuf_off = buf_off;
  glob3_pathend_off = buf_off;
  glob3_pathlim_off = bound_off;
  glob3_pattern_off = pattern_off;

  glob3_dc = 0;
  for (;;)
    if (glob3_pathend_off + glob3_dc >= glob3_pathlim_off) break;
    else {
      //      A[glob3_dc] = 1;
      glob3_dc++;
      /* OK */
      static_assert(0 <= glob3_dc);
      static_assert (glob3_dc < MAXPATHLEN + 1);
      if (unknown()) goto END;
    }
 END:  return 0;
}
