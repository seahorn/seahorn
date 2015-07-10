extern int nd();

int main ()
{
  int a = nd ();
  int y=0;
  if (a != 0)
  {
    y=1;
  }
  if (y==0)
  {
    //assert (a != 0);
    if (a == 0)
      goto ERROR;
  }
  y++;
  
  return 42;
  
ERROR: goto ERROR;
}
