// RUN: %sea smt %s --step=small --inline -o %t.sm.inline.smt2
// RUN: %z3 %t.sm.inline.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// RUN: %sea smt %s --step=large --inline -o %t.lg.inline.smt2
// RUN: %z3 %t.lg.inline.smt2 fp.spacer.order_children=2 2>&1 | OutputCheck %s
//
// CHECK: ^unsat$

// This set of tests is inspired by "Automatic Inference of Class Invariants" by Francesco Logozzo in VMCAI 2014.
// This test case encodes the StackWithUndo class given by Fig. 2.

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
extern int nd9(void);
extern int nd10(void);

extern bool infer(int size, int pos, int stack_size, int undoObject, int undoType);
bool PARTIAL_FN inv(int size, int pos, int stack_size, int undoObject, int undoType)
{
    return infer(size, pos, stack_size, undoObject, undoType);
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
// Encoding of Stack from Fig 2.
//

struct StackWithUndo
{
  // Stack.
  int size;
  int pos;
  struct MockObjectArray stack;
  // StackWithUndo.
  int undoObject;
  int undoType;
};

void New_Stack(struct StackWithUndo *stack, int *exception, int size)
{
  stack->size = Math_Max(size, 1);
  stack->pos = 0;
  New_MockObjectArray(&stack->stack, exception, stack->size);
  /* CHECK FOR EXCEPTIONS */ if (exception != EXCEPTION__NONE) return;
}

void New_StackWithUndo(struct StackWithUndo *stack, int *exception, int size)
{
  stack->undoObject = 0;
  stack->undoType = 0;
  New_Stack(stack, exception, size);
  /* CHECK FOR EXCEPTIONS */ if (exception != EXCEPTION__NONE) return;
}

bool Stack_isEmpty(struct StackWithUndo *stack)
{
  return (stack->pos <= 0);
}

bool Stack_isFull(struct StackWithUndo *stack)
{
  return (stack->pos >= stack->size);
}

int Stack_top(struct StackWithUndo *stack, int *exception)
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

void Stack_push(struct StackWithUndo *stack, int *exception, int o)
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

void StackWithUndo_push(struct StackWithUndo *stack, int *exception, int o)
{
  Stack_push(stack, exception, o);
  /* CHECK FOR EXCEPTIONS */ if (exception != EXCEPTION__NONE) return;
  stack->undoType = 1;
}

void Stack_pop(struct StackWithUndo *stack, int *exception)
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

void StackWithUndo_pop(struct StackWithUndo *stack, int *exception)
{
  int tmp = stack->undoObject;
  if (!Stack_isEmpty(stack))
  {
    int tmp = MockObjectArray_read(&stack->stack, exception, stack->pos - 1);
    /* CHECK FOR EXCEPTIONS */ if (exception != EXCEPTION__NONE) return;
  }
  Stack_pop(stack, exception);
  /* CHECK FOR EXCEPTIONS */ if (exception != EXCEPTION__NONE) return;
  stack->undoType = -1;
  stack->undoObject = tmp;
}

void StackWithUndo_undo(struct StackWithUndo *stack, int *exception)
{
  if (stack->undoType == -1)
  {
    Stack_push(stack, exception, stack->undoObject);
    /* CHECK FOR EXCEPTIONS */ if (exception != EXCEPTION__NONE) return;
    stack->undoType = 0;
  }
  else if (stack->undoType == 1)
  {
    Stack_pop(stack, exception);
    /* CHECK FOR EXCEPTIONS */ if (exception != EXCEPTION__NONE) return;
    stack->undoType = 0;
  }
}

//
// Harness.
//

void Assume_Struct(struct StackWithUndo *stack)
{
  stack->size = nd2();
  stack->pos = nd3();
  stack->stack.size = nd4();
  stack->undoObject = nd5();
  stack->undoType = nd6();
  assume(inv(stack->size, stack->pos, stack->stack.size, stack->undoObject, stack->undoType));
}

void Assert_Struct(struct StackWithUndo *stack)
{
  sassert(inv(stack->size, stack->pos, stack->stack.size, stack->undoObject, stack->undoType));
}

int ApplyOperation(struct StackWithUndo *stack, int op)
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
    StackWithUndo_push(stack, &exception, nd7());
    break;
  case 4:
    StackWithUndo_pop(stack, &exception);
    break;
  default:
    StackWithUndo_undo(stack, &exception);
  }
  return exception;
}

int SelectOperation(struct StackWithUndo *stack)
{
  return ApplyOperation(stack, nd8());
}

int main(void)
{
  // This harness claims that push never returns a StackError exception.
  // The claim is false, since push raises StackError whenever stack->pos == stack->size.
  // Furthermore, stack->pos == stack->size after calling push stack->size times.

  int rule = nd9();
  if (rule == 0)
  {
    // Base case.
    struct StackWithUndo s;
    int exception = EXCEPTION__NONE;
    New_StackWithUndo(&s, &exception, nd10());
    Assert_Struct(&s);
  }
  else if (rule == 1)
  {
    // Inductive case.
    struct StackWithUndo s;
    Assume_Struct(&s);
    SelectOperation(&s);
    Assert_Struct(&s);
  }
  else
  {
    // Safety condition.
    struct StackWithUndo s;
    Assume_Struct(&s);
    sassert(ApplyOperation(&s, 3) != EXCEPTION__STACK);
  }
}
