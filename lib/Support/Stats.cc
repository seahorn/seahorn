#include "seahorn/Support/Stats.hh"
#include <iostream>

namespace seahorn {
std::map<std::string, unsigned> Stats::counters;
std::map<std::string, Stopwatch> Stats::sw;
std::map<std::string, Averager> Stats::av;
std::map<std::string, std::string> Stats::ss;

void Stats::count(const std::string &name) { ++counters[name]; }
double Stats::avg(const std::string &n, double v) { return av[n].add(v); }
unsigned Stats::uset(const std::string &n, unsigned v) {
  return counters[n] = v;
}
unsigned Stats::get(const std::string &n) { return counters[n]; }

void Stats::sset(const std::string &n, const std::string &v) { ss[n] = v; }
std::string &Stats::sget(const std::string &n) { return ss[n]; }

void Stats::start(const std::string &name) { sw[name].start(); }
void Stats::stop(const std::string &name) { sw[name].stop(); }
void Stats::resume(const std::string &name) { sw[name].resume(); }

/** Outputs all statistics to std output */
void Stats::Print(std::ostream &OS) {
  for (auto &kv : ss)
    OS << kv.first << ": " << kv.second << "\n";
  for (auto &kv : counters)
    OS << kv.first << ": " << kv.second << "\n";
  for (auto &kv : sw)
    OS << kv.first << ": " << kv.second << "\n";

  for (auto &kv : av)
    OS << kv.first << ": " << kv.second << "\n";
}

void Stats::PrintBrunch(llvm::raw_ostream &OS) {
  OS << "\n\n************** BRUNCH STATS ***************** \n";
  for (auto &kv : ss)
    OS << "BRUNCH_STAT " << kv.first << " " << kv.second << "\n";

  for (auto &kv : counters)
    OS << "BRUNCH_STAT " << kv.first << " " << kv.second << "\n";

  for (auto &kv : sw)
    OS << "BRUNCH_STAT " << kv.first << " "
       << llvm::format("%.2f", (kv.second).toSeconds()) << "\n";

  for (auto &kv : av)
    OS << "BRUNCH_STAT " << kv.first << " " << kv.second << "\n";

  OS << "************** BRUNCH STATS END ***************** \n";
}

void Stats::Print(llvm::raw_ostream &OS) {
  OS << "\n\n************** STATS ***************** \n";
  for (auto &kv : ss)
    OS << kv.first << ": " << kv.second << "\n";
  for (auto &kv : counters)
    OS << kv.first << ": " << kv.second << "\n";

  for (auto &kv : sw)
    OS << kv.first << ": " << kv.second << "\n";

  for (auto &kv : av)
    OS << kv.first << ": " << kv.second << "\n";

  OS << "************** STATS END ***************** \n";
}

void Stopwatch::Print(std::ostream &out) const {
  long time = getTimeElapsed();
  long h = time / 3600000000L;
  long m = time / 60000000L - h * 60;
  float s = ((float)time / 1000000L) - m * 60 - h * 3600;

  if (h > 0)
    out << h << "h";
  if (m > 0)
    out << m << "m";
  out << s << "s";
}

void Stopwatch::Print(llvm::raw_ostream &out) const {
  long time = getTimeElapsed();
  long h = time / 3600000000L;
  long m = time / 60000000L - h * 60;
  float s = ((float)time / 1000000L) - m * 60 - h * 3600;

  if (h > 0)
    out << h << "h ";
  if (m > 0)
    out << m << "m ";
  out << llvm::format("%.2f", s) << "s";
}

void Averager::Print(std::ostream &out) const { out << avg; }

} // namespace seahorn
