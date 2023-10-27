// -*- verilog -*-
/*! Wrapper used to connect the BRAM model with Kôika !*/
module ext_mem(input CLK, input RST_N, input[69:0] arg1, output[69:0] out1, input[69:0] arg2, output[69:0] out2);
   wire get_valid1;
   wire put_valid1;
   wire[67:0] put_request1;
   assign {get_valid1, put_valid1, put_request1} = arg1;

   wire get_ready1;
   wire put_ready1;
   wire [67:0] get_response1;
   assign out1 = {get_ready1, put_ready1, get_response1};

   wire        get_valid2;
   wire        put_valid2;
   wire [67:0] put_request2;
   assign {get_valid2, put_valid2, put_request2} = arg2;

   wire        get_ready2;
   wire        put_ready2;
   wire [67:0] get_response2;
   assign out2 = {get_ready2, put_ready2, get_response2};

   
`ifndef STDERR
 `define STDERR 32'h80000002
`endif

`ifndef MEM_ADDRESS_WIDTH
 `define MEM_ADDRESS_WIDTH 16
   initial $fwrite(`STDERR,
                   "MEM_ADDRESS_WIDTH unset, defaulting to %d",
                   `MEM_ADDRESS_WIDTH);
`endif

   memory #(.ADDRESS_WIDTH(`MEM_ADDRESS_WIDTH))
   m(.CLK(CLK), .RST_N(RST_N),
     .get_valid1(get_valid1), .put_valid1(put_valid1), .put_request1(put_request1),
     .get_ready1(get_ready1), .put_ready1(put_ready1), .get_response1(get_response1),
     .get_valid2(get_valid2), .put_valid2(put_valid2), .put_request2(put_request2),
     .get_ready2(get_ready2), .put_ready2(put_ready2), .get_response2(get_response2));
endmodule
