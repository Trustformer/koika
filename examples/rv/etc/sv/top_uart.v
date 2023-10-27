// -*- verilog -*-
/*! Verilog wrapper for the Kôika core with a UART interface !*/
// This toplevel is a good starting point to connect directly to a UART receiver
module top_uart(input CLK, input RST_N, output [11:0] LEDS, input uart_line_in, output uart_line_out);
   wire[69:0] dmem_out;
   wire[69:0] dmem_arg;

   wire[69:0] imem_out;
   wire[69:0] imem_arg;

   wire[8:0] uart_wr_opt_byte;
   wire uart_wr_ready;

   wire [8:0] uart_rd_opt_byte;

   wire       uart_read;

   wire led_wr_valid;
   wire led_wr_data;

   reg led = 1'b0;

   wire [2:0] uart_state;

   uart comms(.CLK(CLK), .RST_N(RST_N),
              .read_byte_arg(uart_wr_ready),
              .read_byte_out(uart_wr_opt_byte),
              .write_bit_arg(uart_line_out),
              .write_bit_out(1'b0),
              .write_byte_arg(uart_rd_opt_byte),
              .write_byte_out(1'b0),
              .read_bit_arg(),
              .read_bit_out(uart_line_in),
              .consume_arg(),
              .consume_out(uart_read),
              .show_state_arg(uart_state),
              .show_state_out(1'b0));

   rv32 core(.CLK(CLK), .RST_N(RST_N),

             .ext_mem_dmem_arg(dmem_arg),
             .ext_mem_dmem_out(dmem_out),

             .ext_mem_imem_arg(imem_arg),
             .ext_mem_imem_out(imem_out),

             .ext_uart_write_arg(uart_wr_opt_byte),
             .ext_uart_write_out(uart_wr_ready),

             .ext_uart_read_arg(uart_read),
             .ext_uart_read_out(uart_rd_opt_byte),

             .ext_led_arg({led_wr_valid, led_wr_data}),
             .ext_led_out(led));

   // ext_mem imem(.CLK(CLK), .RST_N(RST_N), .arg(imem_arg), .out(imem_out));
   ext_mem dmem(.CLK(CLK), .RST_N(RST_N),
                .arg1(imem_arg), .out1(imem_out),
                .arg2(dmem_arg), .out2(dmem_out));

   always @(posedge CLK)
     if (led_wr_valid)
       led <= led_wr_data;


   assign LEDS[0] = led;
   assign LEDS[3] = uart_state[0];
   assign LEDS[6] = uart_state[1];
   assign LEDS[9] = uart_state[2];

   assign LEDS[1:2] = 2'b11;
   assign LEDS[4:5] = 2'b11;
   assign LEDS[7:8] = 2'b11;
   assign LEDS[10:11] = 2'b11;
   
   
`ifndef STDERR
 `define STDERR 32'h80000002
`endif

`ifdef SIMULATION
   wire uart_wr_valid = uart_wr_opt_byte[8];
   always @(posedge CLK) begin
      if (uart_wr_ready && uart_wr_valid)
        $fwrite(`STDERR, "%c", uart_wr_opt_byte[7:0]);
   end
`endif
endmodule

// Local Variables:
// flycheck-verilator-include-path: ("../../_objects/rv32i.v/")
// End:
