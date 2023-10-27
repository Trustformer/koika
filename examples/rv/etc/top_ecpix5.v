// -*- verilog -*-
/*! Verilog wrapper for the Kôika core (for use in FPGA synthesis, with a UART interface) !*/
module top_ecpix5(input clk100,
                  input rst,
                 // input [6:0]  btn,
                 output [11:0] leds,
                 output uart_rx, input uart_tx);

   // reg [3:0] counter = 0;
   // wire RST_N = counter[3];
   // always @(posedge clk100)
   //   counter <= counter + {3'b0, ~RST_N};

   top_uart core(.CLK(clk100), .RST_N(rst), .LEDS(leds),
                 .uart_line_in(uart_tx), .uart_line_out(uart_rx));
endmodule

// Local Variables:
// flycheck-verilator-include-path: ("../../_objects/rv32i.v/")
// End:
