# simple statistics module

import resource

def _systemtime ():
  ru_self = resource.getrusage (resource.RUSAGE_SELF)
  ru_ch = resource.getrusage (resource.RUSAGE_CHILDREN)
  return ru_self.ru_utime + ru_ch.ru_utime

class Stopwatch:
  """ A stop watch """
  def __init__ (self):
    self._started = 0
    self._finished = -1
    self._elapsed = 0
    self.start ()
        
        
  @property
  def elapsed (self): 
    """ Returns time (in seconds) since the stopwatch has been started. """
    if self._finished < self._started:
        return self._elapsed + (_systemtime () - self._started)
    return self._elapsed + (self._finished - self._started)
    
  def start (self):
    """ Starts or resumes the stopwatch """
    # collect elapsed time so far
    if self._finished >= self._started:
        self._elapsed += (self._finished - self._started)

    self._started = _systemtime ()
    self._finished = -1

  def stop (self):
    """ Stops the stopwatch """
    if self._finished < self._started:
      self._finished = _systemtime ()

  def reset (self):
    """ Resets the stopwatch by erasing all elapsed time """
    self._elapsed = 0
    self._finished = -1
    self.start ()

  def __str__ (self):
      """ Reports time in seconds up to two decimal places """
      return "{0:.2f}".format (self.elapsed)



def lap (name):
    class ContextManager (object):
        def __init__ (self, name):
            self._name = name
            self._sw = Stopwatch ()
        def __enter__ (self):
            self._sw.reset ()
            return None
        def __exit__ (self, exc_type, exc_value, traceback):
            print('DONE', name, 'in', str(self._sw))
            return False
    return ContextManager (name)
  


_statistics = dict()

def get (key):
    """ Gets a value from statistics table """
    return _statistics.get (key)
def put (key, v): 
    """ Puts a value in statistics table """
    _statistics[key] = v

def start (key): 
    """ Starts (or resumes) a named stopwatch """
    sw = get (key)
    if sw is None:
        sw = Stopwatch ()
        put (key, sw)
        return sw
    else:
        sw.start ()
def stop (key):
    """ Stops a named stopwatch """
    sw = get (key)
    if sw is not None: sw.stop ()

def count (key):
    """ Increments a named counter """
    c = get (key)
    if c is None: put (key, 1)
    else: put (key, c + 1)

def brunch_print ():
    """ Prints the result in brunch format """
    print('----------------------------------------------------------------------')
    for k in sorted (_statistics.keys ()):
        print('BRUNCH_STAT {name} {value}'.format (name=k, value=_statistics [k]))
    print('----------------------------------------------------------------------')
        


def timer (key):
    """ ContextManager to help measuring time. 
    
        with timer('myname') as t:
            do_code_that_is_timed
    """
    class TimerContextManager (object):
        def __init__ (self, key):
            self._key = key
        def __enter__ (self):
            start (key)
            return None
        def __exit__ (self, exc_type, exc_value, traceback):
            stop (key)
            return False
    return TimerContextManager (key)


def block(mark):
    class BlockMarkerContextManager (object):
        def __init__ (self, mark):
            self._mark = mark
        def __enter__ (self):
            print('BEGIN:', mark)
            return None
        def __exit__ (self, exc_type, exc_value, traceback):
            print('END:', mark)
            return False
    return BlockMarkerContextManager (mark)

def count_stats (f):
    def counted_func (*args, **kwds):
        count (f.__module__ + "." + f.__name__ + ".cnt")
        return f(*args, **kwds)
    counted_func.__name__ = f.__name__
    counted_func.__doc__ = f.__doc__
    return counted_func
    
def time_stats (f):
    """ Function decorator to time a function
     
        @time_stats
        def foo (): pass
    """
    def timed_func (*args, **kwds):
        count (f.__module__ + "." + f.__name__ + ".cnt")        
        with timer (f.__module__ + '.' + f.__name__):
            return f(*args, **kwds)
    timed_func.__name__ = f.__name__
    timed_func.__doc__ = f.__doc__
    return timed_func
    
@time_stats
def _test_function ():
    c = 0
    while c < 100000000: c += 1


if __name__ == '__main__':
    import time
    c= 0
    count ('tick')
    with timer ('timer') as t:
        while c < 10000000: c += 1


    brunch_print ()

    c = 0
    count ('tick')
    with timer ('timer') as t:
        while c < 10000000: c += 1


    brunch_print ()
    
    _test_function ()
    brunch_print ()
