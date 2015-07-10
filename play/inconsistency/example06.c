extern int nd ();

int main ()
{

  int x = nd();
  int y=x;
  int flag = 0;

  do 
  {
	if (y==x) {
		flag = 1;
	}
	y++;
	x--;
  } while ( x > 0 );

  if(flag!=0) goto ERROR;

  return x;
  ERROR: goto ERROR;
}
