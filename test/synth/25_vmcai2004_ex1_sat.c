// RUN: %sea smt %s --step=small --inline -o %t.sm.inline.smt2
// RUN: %z3 %t.sm.inline.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// RUN: %sea smt %s --step=large --inline -o %t.lg.inline.smt2
// RUN: %z3 %t.lg.inline.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// CHECK: ^unsat$

// This set of tests is inspired by "Automatic Inference of Class Invariants" by Francesco Logozzo in VMCAI 2014.
// This test case encodes the Stack class given by Fig. 1.

#include "seahorn/seasynth.h"

// In this example, exceptions are encoded as implicit arguments passed between throwing methods.
// Since only the exception type matters in this example, each exception is encoded by a unique integer.
// Exception handling is instrumented into the call site (for example, line A to line B).
#define EXCEPTION__NONE 0
#define EXCEPTION__OUT_OF_BOUNDS 1
#define EXCEPTION__NEGATIVE_SIZE 2
#define EXCEPTION__STACK 3

extern int nd1(void);
extern int nd2(void);
extern int nd3(void);
extern int nd4(void);
extern int nd5(void);
extern int nd6(void);
extern int nd7(void);
extern int nd8(void);

extern bool infer(int size, int pos, int stack_size);
bool PARTIAL_FN inv(int size, int pos, int stack_size)
{
    return infer(size, pos, stack_size);
}

//
// Library methods assumed by the example in Fig 1.
//

int Math_Max(int a, int b)
{
  if (a < b) return b;
  else return a;
}

//
// Mock implementation of Object[].
//

struct MockObjectArray
{
  int size;
};

void New_MockObjectArray(struct MockObjectArray *array, int *exception, int size)
{
  if (size > 0)
  {
    array->size = size;
  }
  else
  {
    array->size = 0;
    *exception = EXCEPTION__NEGATIVE_SIZE;
  }
}

int MockObjectArray_read(struct MockObjectArray *array, int *exception, int i)
{
  if (array->size > i)
  {
    return nd1();
  }
  else
  {
    *exception = EXCEPTION__OUT_OF_BOUNDS;
    return 0;
  }
}

void MockObjectArray_write(struct MockObjectArray *array, int *exception, int i, int o)
{
  if (array->size > i)
  {
    (void) o;
    return;
  }
  else
  {
    *exception = EXCEPTION__OUT_OF_BOUNDS;
  }
}

//
// Encoding of Stack from Fig 1.
//

struct Stack
{
  int size;
  int pos;
  struct MockObjectArray stack;
};

void New_Stack(struct Stack *stack, int *exception, int size)
{
  stack->size = Math_Max(size, 1);
  stack->pos = 0;
  New_MockObjectArray(&stack->stack, exception, stack->size);
  /* CHECK FOR EXCEPTIONS */ if (exception != EXCEPTION__NONE) return;
}

bool Stack_isEmpty(struct Stack *stack)
{
  return (stack->pos <= 0);
}

bool Stack_isFull(struct Stack *stack)
{
  return (stack->pos >= stack->size);
}

int Stack_top(struct Stack *stack, int *exception)
{
  if (!Stack_isEmpty(stack))
  {
    int tmp = MockObjectArray_read(&stack->stack, exception, stack->pos - 1); // Line A.
    /* CHECK FOR EXCEPTIONS */ if (exception != EXCEPTION__NONE) return 0;
    return tmp; // Line B.
  }
  else
  {
    *exception = EXCEPTION__STACK;
    return 0;
  }
}

void Stack_push(struct Stack *stack, int *exception, int o)
{
  if (!Stack_isFull(stack))
  {
    MockObjectArray_write(&stack->stack, exception, stack->pos, o);
    /* CHECK FOR EXCEPTIONS */ if (exception != EXCEPTION__NONE) return;
    stack->pos = stack->pos + 1;
  }
  else
  {
    *exception = EXCEPTION__STACK;
  }
}

void Stack_pop(struct Stack *stack, int *exception)
{
  if (!Stack_isEmpty(stack))
  {
    stack->pos = stack->pos - 1;
  }
  else
  {
    *exception = EXCEPTION__STACK;
  }
}

//
// Harness.
//

void Assume_Struct(struct Stack *stack)
{
  stack->size = nd2();
  stack->pos = nd3();
  stack->stack.size = nd4();
  assume(inv(stack->size, stack->pos, stack->stack.size));
}

void Assert_Struct(struct Stack *stack)
{
  sassert(inv(stack->size, stack->pos, stack->stack.size));
}

int ApplyOperation(struct Stack *stack, int op)
{
  int exception = EXCEPTION__NONE;
  switch (op)
  {
  case 0:
    Stack_isEmpty(stack);
    break;
  case 1:
    Stack_isFull(stack);
    break;
  case 2:
    Stack_top(stack, &exception);
    break;
  case 3:
    Stack_push(stack, &exception, nd6());
    break;
  default:
    Stack_pop(stack, &exception);
    break;
  }
  return exception;
}

int SelectOperation(struct Stack *stack)
{
  return ApplyOperation(stack, nd5());
}

int main(void)
{
  // This harness claims that push never returns a StackError exception.
  // The claim is false, since push raises StackError whenever stack->pos == stack->size.
  // Furthermore, stack->pos == stack->size after calling push stack->size times.

  int rule = nd7();
  if (rule == 0)
  {
    // Base case.
    struct Stack s;
    int exception = EXCEPTION__NONE;
    New_Stack(&s, &exception, nd8());
    Assert_Struct(&s);
  }
  else if (rule == 1)
  {
    // Inductive case.
    struct Stack s;
    Assume_Struct(&s);
    SelectOperation(&s);
    Assert_Struct(&s);
  }
  else
  {
    // Safety condition.
    struct Stack s;
    Assume_Struct(&s);
    sassert(ApplyOperation(&s, 3) != EXCEPTION__STACK);
  }
}
