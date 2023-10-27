// -*- verilog -*-
/*! Verilog model of a BRAM !*/
`define REQ_ADDR_WIDTH 32
`define REQ_DATA_WIDTH 32
`define MEM_OP_SIZE (4 + `REQ_ADDR_WIDTH + `REQ_DATA_WIDTH)

module memory(input  CLK,
              input                       RST_N,
              input                       get_valid1,
              input                       put_valid1,
              input [`MEM_OP_SIZE - 1:0]  put_request1,
              output                      get_ready1,
              output                      put_ready1,
              output [`MEM_OP_SIZE - 1:0] get_response1
              ,
              input                       get_valid2,
              input                       put_valid2,
              input [`MEM_OP_SIZE - 1:0]  put_request2,
              output                      get_ready2,
              output                      put_ready2,
              output [`MEM_OP_SIZE - 1:0] get_response2
);
   parameter ADDRESS_WIDTH = 14;
   parameter EXIT_ADDRESS = `REQ_ADDR_WIDTH'h40001000;

   reg has_request1;
   reg [`MEM_OP_SIZE - 1:0] last_request1;
   reg                      has_request2;
   reg [`MEM_OP_SIZE - 1:0] last_request2;

`ifndef STDERR
 `define STDERR 32'h80000002
`endif

`ifdef BROKEN_READMEMH
 // The implementation of $readmemh in CVC is broken.  It only loads one entry
 // if both endpoints of the file's range are not specified, and it complains
 // about the final address if it corresponds to the final index.
 `define MEMSIZE (1 << ADDRESS_WIDTH) + 1
`else
 `define MEMSIZE (1 << ADDRESS_WIDTH)
`endif

   reg [`REQ_DATA_WIDTH - 1:0] mem[`MEMSIZE - 1:0];

`ifdef BRAM_RUNTIME_INIT
   wire[8 * 256 - 1:0] filename;
   initial
     begin : init_rom_block
      if ($value$plusargs("VMH=%s", filename)) begin
         // Omitting the last argument to ‘$readmemh’ would prevent complaints
         // when the ‘mem’ array is larger than the image stored in ‘filename’.
         $readmemh(filename, mem, 0, `MEMSIZE - 1);
      end else begin
         $fwrite(`STDERR, "ERROR: No memory image loaded. Use +VMH=<path> to load one\n");
         $finish(1'b1);
      end
   end
`else
 `ifndef MEM_FILENAME
   // We use a macro instead of a parameter because Yosys instantiates the
   // module with its default parameters when it first reads it (See
   // https://www.reddit.com/r/yosys/comments/f92bke/)
  `define MEM_FILENAME "MEM_FILENAME_UNSET"
 `endif
   initial
     begin : init_rom_block
        $readmemh(`MEM_FILENAME, mem, 0, `MEMSIZE - 1);
     end
`endif

   function[ADDRESS_WIDTH - 1:0] translate_address(input[`REQ_ADDR_WIDTH - 1:0] address);
      reg[`REQ_ADDR_WIDTH - 1:0] _untruncated_addr;
      begin
         _untruncated_addr = address >> 2;
         translate_address = _untruncated_addr[ADDRESS_WIDTH - 1:0];
      end
   endfunction

   function[`REQ_DATA_WIDTH - 1:0] compute_mask(input[3:0] byte_en);
      compute_mask = {{8{byte_en[3]}}, {8{byte_en[2]}}, {8{byte_en[1]}}, {8{byte_en[0]}}};
   endfunction

   function[`REQ_DATA_WIDTH - 1:0] compute_update(input [`REQ_DATA_WIDTH - 1:0] mask,
                                                  input [`REQ_DATA_WIDTH - 1:0] data,
                                                  input [`REQ_DATA_WIDTH - 1:0] original);
      begin
         compute_update = (original & ~mask) | (data & mask);
      end
   endfunction // compute_update
   
   wire [3:0] put_request_byte_en1;
   wire [`REQ_ADDR_WIDTH - 1:0] put_request_addr1;
   wire [`REQ_DATA_WIDTH - 1:0] put_request_data1;
   assign {put_request_byte_en1, put_request_addr1, put_request_data1} = put_request1;

   wire [3:0]                   last_request_byte_en1;
   wire [`REQ_ADDR_WIDTH - 1:0] last_request_addr1;
   wire [`REQ_DATA_WIDTH - 1:0] last_request_data1;
   assign {last_request_byte_en1, last_request_addr1, last_request_data1} = last_request1;

   wire [ADDRESS_WIDTH - 1:0]   addr1 = translate_address(last_request_addr1);
   wire [`REQ_DATA_WIDTH - 1:0] data1 = mem[addr1];

   assign get_ready1 = RST_N && has_request1;
   assign put_ready1 = RST_N && (get_valid1 || !has_request1);

   wire [`REQ_DATA_WIDTH - 1:0] get_response_data1 = last_request_byte_en1 == 4'b0000 ? data1 : 0;
   assign get_response1 = {last_request_byte_en1, last_request_addr1, get_response_data1};

   wire                         put_wf1 = put_valid1 && put_ready1;
   wire                         get_wf1 = get_valid1 && get_ready1;

   wire [3:0] put_request_byte_en2;
   wire [`REQ_ADDR_WIDTH - 1:0] put_request_addr2;
   wire [`REQ_DATA_WIDTH - 1:0] put_request_data2;
   assign {put_request_byte_en2, put_request_addr2, put_request_data2} = put_request2;

   wire [3:0] last_request_byte_en2;
   wire [`REQ_ADDR_WIDTH - 1:0] last_request_addr2;
   wire [`REQ_DATA_WIDTH - 1:0] last_request_data2;
   assign {last_request_byte_en2, last_request_addr2, last_request_data2} = last_request2;

   wire[ADDRESS_WIDTH - 1:0] addr2 = translate_address(last_request_addr2);
   wire[`REQ_DATA_WIDTH - 1:0] data2 = mem[addr2];

   assign get_ready2 = RST_N && has_request2;
   assign put_ready2 = RST_N && (get_valid2 || !has_request2);

   wire[`REQ_DATA_WIDTH - 1:0] get_response_data2 = last_request_byte_en2 == 4'b0000 ? data2 : 0;
   assign get_response2 = {last_request_byte_en2, last_request_addr2, get_response_data2};

   wire put_wf2 = put_valid2 && put_ready2;
   wire get_wf2 = get_valid2 && get_ready2;

   always @(posedge CLK) begin
      if (RST_N == 1) begin
         // NO UPDATE FOR addr1
         // If we attempt to update, yosys fails to recognize this module as something memory-like and tries using FFs instead of BRAM.
         if (has_request2) begin
            mem[addr2] <= compute_update(compute_mask(last_request_byte_en2), last_request_data2, data2);
         end

         if (put_wf1) begin
            last_request1 <= put_request1;
         end
         if (put_wf2) begin
            last_request2 <= put_request2;
         end

         has_request1 <= put_wf1 || (has_request1 && !get_wf1);
         has_request2 <= put_wf2 || (has_request2 && !get_wf2);
      end else begin
         has_request1 <= 1'b0;
         has_request2 <= 1'b0;
      end
  end
endmodule
