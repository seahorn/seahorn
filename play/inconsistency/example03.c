// SPDX-FileCopyrightText: 2026 The SeaHorn Authors
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#include <stdio.h>

extern int nd ();

int main ()
{
  int x = 0;
  if (nd ())
    x++;
  else
    x+=3;

  if (nd ())
    x++;
  else
    x+=3;

  if (nd ())
    x++;
  else
    x+=3;

  if (nd ())
    x++;
  else
    x+=3;

  if (nd ())
    x++;
  else
    x+=3;

  if (x == 8)
  {
    printf ("hello world\n");
  }

  return 42;
}
