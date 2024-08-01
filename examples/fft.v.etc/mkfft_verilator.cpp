// A Verilator driver for the Bluespec implementation of the fft.v example
// Derived from ocaml/backends/resources/verilator.cpp
#include "verilator.hpp"
#include "Vmkfft.h"

class TB : public KoikaToplevel<Vmkfft> {
  using KoikaToplevel<Vmkfft>::dut;

public:
  void run(uint64_t ncycles) {
    KoikaToplevel<Vmkfft>::run(ncycles);
    printf("%d", dut.rd);
  }

  TB() : KoikaToplevel<Vmkfft>{} {}
};

int main(int argc, char** argv) {
  return _main<TB>(argc, argv);
}
