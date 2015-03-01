
int unknown1();
int unknown2();

void main(int flag)
{
  int x = 1;
  int y = 1;
  int a;
  
  if(flag)
    a = 0;
  else
    a = 1;

  while(unknown1()){
    if(flag)
    {
      a = x+y;
      x++;
    }
    else
    {
      a = x+y+1;
      y++;
    }
    if(a%2==1)
      y++;
    else
      x++;	  
  }
  //x==y

  if(flag)
    a++;
  static_assert(a%2==1);
}
