/* extern void __VERIFIER_error(void); */
/* void assert (int v) {if (!v) __VERIFIER_error ();} */


extern int nd ();
//int y =0;

int foo ()
{
  int x= nd ();
  if (x<0)
    x--;
  else 
    x++;

  if (x <= 0) // assert (x>0);
    goto NOTTERMINATE;  
  return x;

NOTTERMINATE: goto NOTTERMINATE;
}

int main ()
{
  int a = foo (); //nd ();
  int y=0;
  if (a != 0)
  {
    y=1;
  }
  if (y==0)
  {
    //assert (a != 0);
    if (a == 0)
      goto NOTTERMINATE;
  }
  y++;
  
  return 42;
  
NOTTERMINATE: goto NOTTERMINATE;
}
