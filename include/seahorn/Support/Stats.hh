#pragma once

#include <map>

#include <sys/resource.h>
#include <sys/time.h>

#include "llvm/Support/Format.h"
#include "llvm/Support/raw_ostream.h"
#include <iosfwd>

namespace seahorn {
class Stopwatch {
private:
  long started;
  long finished;
  long timeElapsed;

  long systemTime() const {
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    long r = ru.ru_utime.tv_sec * 1000000L + ru.ru_utime.tv_usec;
    return r;
  }

public:
  Stopwatch() { start(); }

  void start() {
    started = systemTime();
    finished = -1;
    timeElapsed = 0;
  }

  void stop() {
    if (finished < started) {
      finished = systemTime();
    }
  }

  void resume() {
    if (finished >= started) {
      timeElapsed += finished - started;
      started = systemTime();
      finished = -1;
    }
  }

  long getTimeElapsed() const {
    if (finished < started)
      return timeElapsed + systemTime() - started;
    return timeElapsed + finished - started;
  }

  void Print(std::ostream &out) const;
  void Print(llvm::raw_ostream &out) const;

  double toSeconds() {
    double time = ((double)getTimeElapsed() / 1000000);
    return time;
  }
};

/** Computes running average */
class Averager {
private:
  size_t count;
  double avg;

public:
  Averager() : count(0), avg(0) {}

  double add(double k) {
    avg += (k - avg) / (++count);
    return avg;
  }

  void Print(std::ostream &out) const;

  void Print(llvm::raw_ostream &out) const { out << llvm::format("%.2f", avg); }
};

} // namespace seahorn

namespace seahorn {
inline std::ostream &operator<<(std::ostream &OS, const Stopwatch &sw) {
  sw.Print(OS);
  return OS;
}

inline llvm::raw_ostream &operator<<(llvm::raw_ostream &OS,
                                     const Stopwatch &sw) {
  sw.Print(OS);
  return OS;
}

inline std::ostream &operator<<(std::ostream &OS, const Averager &av) {
  av.Print(OS);
  return OS;
}

inline llvm::raw_ostream &operator<<(llvm::raw_ostream &OS,
                                     const Averager &av) {
  av.Print(OS);
  return OS;
}

class Stats {
private:
  static std::map<std::string, unsigned> counters;
  static std::map<std::string, Stopwatch> sw;
  static std::map<std::string, Averager> av;
  static std::map<std::string, std::string> ss;

public:
  static unsigned get(const std::string &n);
  static double avg(const std::string &n, double v);
  static unsigned uset(const std::string &n, unsigned v);

  static void sset(const std::string &n, const std::string &v);
  static std::string &sget(const std::string &n);

  static void count(const std::string &name);

  static void start(const std::string &name);
  static void stop(const std::string &name);
  static void resume(const std::string &name);

  /** Outputs all statistics to std output */
  static void Print(std::ostream &OS);
  static void Print(llvm::raw_ostream &OS);
  static void PrintBrunch(llvm::raw_ostream &OS);
};

/**
    Usage: add
       auto_timer X("foo.bar");
    at the beginning of a block (i.e., function body, conditional, etc)
    to measure the time it takes to execute.
 */
// class auto_timer
// {
// private:
//   std::string n;
// public:
//   auto_timer (const std::string &name) : n(name) { Stats::resume (n); }
//   ~auto_timer () { Stats::stop (n); }
// };

template <typename Output> class TimeIt {
  const char *m_msg;
  Output &m_out;
  Stopwatch m_sw;
  double m_min;

public:
  TimeIt(const char *msg, Output out, double min = 0.0)
      : m_msg(msg), m_out(out), m_min(min) {}
  ~TimeIt() {
    m_sw.stop();
    if (m_sw.toSeconds() >= m_min)
      m_out << "TimeIt: " << m_msg << " " << m_sw << "\n";
  }
};

class ScopedStats {
  std::string m_name;

public:
  ScopedStats(const std::string &name, bool reset = false) : m_name(name) {
    if (reset) {
      m_name += ".last";
      Stats::start(m_name);
    } else
      Stats::resume(m_name);
  }
  ~ScopedStats() { Stats::stop(m_name); }
};

} // namespace seahorn

#define SEA_MEASURE_FN ScopedStats __stats__(__FUNCTION__)
#define SEA_MEASURE_FN_LAST ScopedStats __stats_last__(__FUNCTION__, true)
