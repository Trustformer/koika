/*! C++ driver for rv32i simulation with Cuttlesim !*/
#include <iostream>
#include <memory>
#include <optional>

#include "rv32.hpp"
#include "elf.hpp"
#include "cuttlesim.hpp"

#define DMEM_SIZE (static_cast<std::size_t>(1) << 25)

struct bram {
  std::unique_ptr<bits<32>[]> mem;
  std::optional<struct_mem_req> last1, last2;

  std::optional<struct_mem_resp> get(bool enable, std::optional<struct_mem_req> &last) {
    if (!enable || !last.has_value())
      return std::nullopt;

    auto data = last->data;
    auto addr = last->addr;
    auto dEn = last->byte_en;
    bits<32> current = bits<32>{0};
    current = mem[addr.v >> 2];
    mem[addr.v >> 2] =
      ((dEn[2'0_d] ? data : current) & 0x32'000000ff_x) |
      ((dEn[2'1_d] ? data : current) & 0x32'0000ff00_x) |
      ((dEn[2'2_d] ? data : current) & 0x32'00ff0000_x) |
      ((dEn[2'3_d] ? data : current) & 0x32'ff000000_x);

    last.reset();
    return std::optional<struct_mem_resp>{{
        .byte_en = dEn, .addr = addr, .data = current
      }};
  }

  bool put(std::optional<struct_mem_req> req, std::optional<struct_mem_req> &last) {
    if (!req.has_value() || last.has_value())
      return false;

    last = *req;
    return true;
  }

  struct_mem_output getput(struct_mem_input req, std::optional<struct_mem_req> &last) {
    std::optional<struct_mem_resp> get_response = get(bool(req.get_ready), last);
    bool put_ready = put(req.put_valid ? std::optional<struct_mem_req>{req.put_request} : std::nullopt, last);
    return struct_mem_output{
      .get_valid = bits<1>{get_response.has_value()},
      .put_ready = bits<1>{put_ready},
      .get_response = get_response.value_or(struct_mem_resp{})
    };
  }

  void read_elf(const std::string& elf_fpath) {
    elf_load(reinterpret_cast<uint32_t*>(mem.get()), elf_fpath.c_str());
  }

  // Use new … instead of make_unique to avoid 0-initialization
  bram() : mem{new bits<32>[DMEM_SIZE]}, last1{}, last2{} {}
};

struct extfuns_t {
  bram dmem;
  bits<1> led;

  struct_mem_output ext_mem_dmem(struct_mem_input req) {
    return dmem.getput(req, dmem.last2);
  }

  struct_mem_output ext_mem_imem(struct_mem_input req) {
    return dmem.getput(req, dmem.last1);
  }

  bits<1> ext_uart_write(struct_maybe_bits_8 req) {
    if (req.valid) {
      putchar(static_cast<char>(req.data.v));
    }
    return req.valid;
  }

  struct_maybe_bits_8 ext_uart_read(bits<1> req) {
    bool valid = req.v;
    return struct_maybe_bits_8 {
      .valid = bits<1>{valid},
      .data = bits<8>{(bits_t<8>)(valid ? getchar() : 0)} };
  }

  bits<1> ext_led(struct_maybe_bits_1 req) {
    bits<1> current = led;
    if (req.valid) {
      led = req.data;
      fprintf(stderr, led.v ? "☀" : "🌣");
    }
    return current;
  }

  enum_hostID ext_host_id(bits<1>) {
    return enum_hostID::Cuttlesim;
  }

  template<typename simulator>
  bits<1> ext_finish(simulator& sim, struct_maybe_bits_8 req) {
    if (req.valid) {
      bits<8> exitcode = req.data;
      if (exitcode == 8'0_b) {
        printf("  [0;32mPASS[0m\n");
      } else {
        printf("  [0;31mFAIL[0m (%d)\n", exitcode.v);
      }
      sim.finish(cuttlesim::exit_info_none, exitcode.v);
    }
    return 1'0_b;
  }

  extfuns_t() : dmem{}, led{false} {}
};

template<size_t len>
std::string hexstr (const bits<len>& b){
  return prims::repr(b, {true, true, prims::hex});
}

void show_mem_req(prims::bits<1> valid, const struct_mem_req& x){
  if(bool(valid)){
    std::cout << "@" << hexstr(x.addr) << "[" <<
      hexstr(x.byte_en) << "] <- " << hexstr(x.data);
  } else {
    std::cout << "invalid";
  }
}


void show_mem_resp(prims::bits<1> valid, const struct_mem_resp& x){
  if(bool(valid)){
    std::cout << "@" << hexstr(x.addr) << "[" <<
      hexstr(x.byte_en) << "] <- " << hexstr(x.data);
  } else {
    std::cout << "invalid";
  }
}

class rv_core final : public module_rv32<extfuns_t> {
  void strobe() const {
#if defined(SIM_STROBE) && !defined(SIM_MINIMAL)
    std::cout << "# " << Log.state.cycle_count << std::endl;
    std::cout << "pc = " << Log.state.pc << std::endl;
    std::cout << "epoch = " << Log.state.epoch << std::endl;
    // std::cout << "inst_count = " << Log.state.instr_count << std::endl;
    // std::cout << "rf = {" << std::endl;
    // std::cout << "  " <<
    //   "[01] (ra) = " << Log.state.rf_rData_1 << "; " <<
    //   "[02] (sp) = " << Log.state.rf_rData_2 << "; " <<
    //   "[03] (gp) = " << Log.state.rf_rData_3 << "; " <<
    //   "[04] (tp) = " << Log.state.rf_rData_4 << std::endl;
    // std::cout << "  [05-07] (t0-t2)     = " <<
    //   Log.state.rf_rData_5 << "; " <<
    //   Log.state.rf_rData_6 << "; " <<
    //   Log.state.rf_rData_7 << std::endl;
    // std::cout << "  [08-09] (s0_fp, s1) = " <<
    //   Log.state.rf_rData_8 << "; " <<
    //   Log.state.rf_rData_9 << std::endl;
    // std::cout << "  [10-17] (a0-a7)     = " <<
    //   Log.state.rf_rData_10 << "; " <<
    //   Log.state.rf_rData_11 << "; " <<
    //   Log.state.rf_rData_12 << "; " <<
    //   Log.state.rf_rData_13 << "; " <<
    //   Log.state.rf_rData_14 << "; " <<
    //   Log.state.rf_rData_15 << "; " <<
    //   Log.state.rf_rData_16 << "; " <<
    //   Log.state.rf_rData_17 << std::endl;
    // std::cout << "  [18-27] (s2-s11)    = " << Log.state.rf_rData_18 << "; " <<
    //   Log.state.rf_rData_19 << "; " <<
    //   Log.state.rf_rData_20 << "; " <<
    //   Log.state.rf_rData_21 << "; " <<
    //   Log.state.rf_rData_22 << "; " <<
    //   Log.state.rf_rData_23 << "; " <<
    //   Log.state.rf_rData_24 << "; " <<
    //   Log.state.rf_rData_25 << "; " <<
    //   Log.state.rf_rData_26 << "; " <<
    //   Log.state.rf_rData_27 << std::endl;
    // std::cout << "  [28-31] (t3-t6)     = " <<
    //   Log.state.rf_rData_28 << "; " <<
    //   Log.state.rf_rData_29 << "; " <<
    //   Log.state.rf_rData_30 << "; " <<
    //   Log.state.rf_rData_31 << std::endl;
    // std::cout << "}" << std::endl;
    std::cout << "toImem = ";
    show_mem_req(Log.state.toIMem_valid0,
                 Log.state.toIMem_data0);
    std::cout << std::endl;

    std::cout << "fromImem = ";
    show_mem_resp(Log.state.fromIMem_valid0,
                  Log.state.fromIMem_data0);
    std::cout << std::endl;

    std::cout << "toDMem = ";
    show_mem_req(Log.state.toDMem_valid0,
                 Log.state.toDMem_data0);
    std::cout << std::endl;

    std::cout << "fromDMem = ";
    show_mem_resp(Log.state.fromDMem_valid0,
                  Log.state.fromDMem_data0);
    std::cout << std::endl;


    // std::cout << "toIMem = { valid0 = " << Log.state.toIMem_valid0
    //           << ", data0 = " << Log.state.toIMem_data0 << " };" <<
    //   "fromIMem = { valid0 = " << Log.state.fromIMem_valid0
    //           << ", data0 = " << Log.state.fromIMem_data0 << " }" << std::endl;
    // std::cout <<
    //   "toDMem = { valid0 = " << Log.state.toDMem_valid0
    //           << ", data0 = " << Log.state.toDMem_data0 << " };" <<
    //   "fromDMem = { valid0 = " << Log.state.fromDMem_valid0
    //           << ", data0 = " << Log.state.fromDMem_data0 << " }" << std::endl;
    std::cout <<
      "f2d        = { valid0 = "
              << bool(Log.state.f2d_valid0)
              << ", data0 = {.pc = "
              << hexstr(Log.state.f2d_data0.pc)
              << ", .ppc = " << hexstr(Log.state.f2d_data0.ppc)
              << ", .epoch = " << hexstr(Log.state.f2d_data0.epoch)
              <<  " };" << std::endl <<
      "f2dprim    = { valid0 = "
              << bool(Log.state.f2dprim_valid0)
              << ", data0 = {.pc = "
              << hexstr(Log.state.f2dprim_data0.pc)
              << ", .ppc = " << hexstr(Log.state.f2dprim_data0.ppc)
              << ", .epoch = " << hexstr(Log.state.f2dprim_data0.epoch)
              <<  " };" << std::endl;
    std::cout <<
      "d2e        = { valid0 = "
              << bool(Log.state.d2e_valid0)
              << ", data0 = {.pc = "
              << hexstr(Log.state.d2e_data0.pc)
              << ", .ppc = " << hexstr(Log.state.d2e_data0.ppc)
              << ", .epoch = " << hexstr(Log.state.d2e_data0.epoch)
              << ".dInst = "
              << hexstr(Log.state.d2e_data0.dInst.inst)
              << ", .legal = " << bool(Log.state.d2e_data0.dInst.legal)
              <<  " };" << std::endl;
    std::cout << "e2w    = { valid0 = "
      << bool(Log.state.e2w_valid0)
      << ", data0 = {.inst = "
      << hexstr(Log.state.e2w_data0.dInst.inst)
      << ", .legal = " << bool(Log.state.e2w_data0.dInst.legal)
      <<  " };" << std::endl;

  
#endif
  }

public:
  explicit rv_core(const std::string& elf_fpath) : module_rv32{} {
    // extfuns.imem.read_elf(elf_fpath);
    extfuns.dmem.read_elf(elf_fpath);
  }
};

#ifdef SIM_MINIMAL
template rv_core::snapshot_t cuttlesim::init_and_run<rv_core>(unsigned long long, std::string&);
#else
int main(int argc, char** argv) {
  if (argc <= 1) {
    std::cerr << "Usage: ./rv_core elf_file [ncycles [vcd_path [vcd_period]]]" << std::endl;
    return 1;
  }

  setbuf(stdout, NULL);
  std::ios_base::sync_with_stdio(false);
  cuttlesim::main<rv_core>(argc - 1, argv + 1, argv[1]);
}
#endif

// Local Variables:
// flycheck-clang-include-path: ("../_objects/rv32i.v/")
// flycheck-clang-language-standard: "c++17"
// End:
