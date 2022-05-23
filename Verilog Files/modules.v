
`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 02/22/2022 04:16:14 PM
// Design Name: 
// Module Name: n_bit_mux2x1
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module n_bit_mux2x1 #(parameter n=32)(input [n-1:0] x, y, input sel,output[n-1:0] out );

assign out=(sel==1'b1)? y:x;

endmodule



`define     IR_rs1          19:15
`define     IR_rs2          24:20
`define     IR_rd           11:7
`define     IR_opcode       6:2
`define     IR_funct3       14:12
`define     IR_funct7       31:25
`define     IR_shamt        24:20

`define     OPCODE_Branch   5'b11_000
`define     OPCODE_Load     5'b00_000
`define     OPCODE_Store    5'b01_000
`define     OPCODE_JALR     5'b11_001
`define     OPCODE_JAL      5'b11_011
`define     OPCODE_Arith_I  5'b00_100
`define     OPCODE_Arith_R  5'b01_100
`define     OPCODE_AUIPC    5'b00_101
`define     OPCODE_LUI      5'b01_101
`define     OPCODE_SYSTEM   5'b11_100 
`define     OPCODE_Custom   5'b10_001

`define     F3_ADD          3'b000
`define     F3_SLL          3'b001
`define     F3_SLT          3'b010
`define     F3_SLTU         3'b011
`define     F3_XOR          3'b100
`define     F3_SRL          3'b101
`define     F3_OR           3'b110
`define     F3_AND          3'b111

`define     BR_BEQ          3'b000
`define     BR_BNE          3'b001
`define     BR_BLT          3'b100
`define     BR_BGE          3'b101
`define     BR_BLTU         3'b110
`define     BR_BGEU         3'b111

`define     OPCODE          IR[`IR_opcode]

`define     ALU_ADD         4'b00_00
`define     ALU_SUB         4'b00_01
`define     ALU_PASS        4'b00_11
`define     ALU_OR          4'b01_00
`define     ALU_AND         4'b01_01
`define     ALU_XOR         4'b01_11
`define     ALU_SRL         4'b10_00
`define     ALU_SRA         4'b10_10
`define     ALU_SLL         4'b10_01
`define     ALU_SLT         4'b11_01
`define     ALU_SLTU        4'b11_11

`define     SYS_EC_EB       3'b000


//////////////////////////////////////////////////////////////////////////////////


/*module ImmGen (input [31:0] inst,output [31:0] gen_out); 

reg [11:0] temp_imm ;

always @(*)
begin
      if (inst[6]==1'b1) begin :beq
         temp_imm = {inst[31],inst[7],inst[30:25],inst [11:8]};
      end 
      else begin: store_Load
        if (inst[5]==1'b1)begin :store
             temp_imm = {inst[31:25],inst [11:7]};  
            end 
            else begin :load
            temp_imm = {inst[31:20]}; 
           end 
            
      end
   end
   
assign  gen_out = {{20{temp_imm[11]}},temp_imm[11:0]};


endmodule
*/




module rv32_ImmGen (
    input  wire [31:0]  IR,
    output reg  [31:0]  Imm);

always @(*) begin
	case (`OPCODE)
		`OPCODE_Arith_I   : 	Imm = { {21{IR[31]}}, IR[30:25], IR[24:21], IR[20] };
		`OPCODE_Store     :     Imm = { {21{IR[31]}}, IR[30:25], IR[11:8], IR[7] };
		`OPCODE_LUI       :     Imm = { IR[31], IR[30:20], IR[19:12], 12'b0 };
		`OPCODE_AUIPC     :     Imm = { IR[31], IR[30:20], IR[19:12], 12'b0 };
		`OPCODE_JAL       : 	Imm = { {12{IR[31]}}, IR[19:12], IR[20], IR[30:25], IR[24:21], 1'b0 };
		`OPCODE_JALR      : 	Imm = { {21{IR[31]}}, IR[30:25], IR[24:21], IR[20] };
		`OPCODE_Branch    : 	Imm = { {20{IR[31]}}, IR[7], IR[30:25], IR[11:8], 1'b0};
		default           : 	Imm = { {21{IR[31]}}, IR[30:25], IR[24:21], IR[20] }; // IMM_I
	endcase 
end

endmodule


module n_bit_reg #(parameter n=32)(input[n-1:0] D, input clk, rst, load, output[n-1:0]Q);
wire [n-1:0]mux_out;

   genvar i;
   generate
      for (i=0; i <n; i=i+1)
      begin: Loop
              Mux2x1 u(Q[i], D[i], load, mux_out[i]);
        DFlipFlop uu1 (clk,rst, mux_out[i],  Q[i]); 
      end
   endgenerate

endmodule


module DFlipFlop
(input clk, input rst, input D, output reg Q); 
 always @ (posedge clk or posedge rst) 
 if (rst) begin 
 Q <= 1'b0; 
 end else begin 
 Q <= D; 
 end 

endmodule

module Mux2x1(input x, y, sel,output out );

assign out=(sel==1'b1)? y:x;

endmodule








module Register_File #(parameter n=32, m=32)
(input [4:0] read_reg_first, read_reg_second , write_reg,
input [n-1:0] write_data,
input reg_write,clk, rst,
output [n-1:0] read_data_first, read_data_second
    );
    
   wire [n-1:0] q [0:m-1]; 
   reg [m-1:0] load;
   
    genvar i;
      generate
         for (i=0; i <m; i=i+1)
         begin: Loop
                 n_bit_reg m1 (write_data, clk, rst, load[i], q[i]);
         end
      endgenerate
 /*   assign  q[1]=32'd3;
    assign  q[2]=32'd2;
    //assign  q[5]=32'd3;
    assign  q[6]=32'd1;
    assign  q[10]=32'd7;
    //assign  q[5]=32'd3;
    assign  q[6]=32'd1;  */  
    
    always@(*)
        begin
            if((reg_write)&&(write_reg!=0))
                 begin
                     load=32'd0;
                     load[write_reg]=1'b1;   
                end
            else
                 begin
                    load=32'd0;
                 end
        end
        
  assign   read_data_first=q[read_reg_first];
  assign   read_data_second=q[read_reg_second];      
        
    
    
    
endmodule






module prv32_ALU(input   wire [31:0] a, b,
input wire AluSrc,
input   wire [4:0]  shamt,
input   wire [3:0]  alufn,
input wire [3:0] funct,
    output  reg  [31:0] r,
	output  wire        cf, zf, vf, sf
);

    wire [31:0] add, sub, op_b;
    wire cfa, cfs;
    
    assign op_b = (~b);
    
    assign {cf, add} = alufn[0] ? (a + op_b + 1'b1) : (a + b);
    
    assign zf = (add == 0);
    assign sf = add[31];
    assign vf = (a[31] ^ (op_b[31]) ^ add[31] ^ cf);
    
    wire[31:0] sh;
    shifter shifter0(.a(a), .shamt(shamt),.b(b),.AluSrc(AluSrc), .type(funct),  .r(sh));
    
    always @ * begin
        r = 0;
        (* parallel_case *)
        case (alufn)
            // arithmetic
            4'b00_00 : r = add;
            4'b00_01 : r = add;
            4'b00_11 : r = b;
            // logic
            4'b01_00:  r = a | b;
            4'b01_01:  r = a & b;
            4'b01_11:  r = a ^ b;
            // shift
            4'b10_00:  r=sh;
            4'b10_01:  r=sh;
            4'b10_10:  r=sh;
            // slt & sltu
            4'b11_01:  r = {31'b0,(sf != vf)}; 
            4'b11_11:  r = {31'b0,(~cf)};            	
        endcase
    end
endmodule

module  shifter (input [31:0] a,input [4:0]  shamt ,input [31:0] b,input AluSrc, input[3:0] type, output reg  [31:0] r);

always @(*)
        if(AluSrc) begin
           case (type)
             4'b0001: r= a << shamt; //slli &SLL
             4'b0101: r= a>>shamt;     //srli srl
             4'b1101: r=  a>>>shamt;      //srai   sra 
            endcase
            end
         else
            begin
              case (type)                                     
                4'b0001: r= a << b; //slli &SLL           
                4'b0101: r= a>>b;     //srli srl          
               4'b1101: r=  a>>>b;      //srai   sra     
              endcase                                        
         end  
endmodule


 

module  RCA  #(parameter n=32)(X, Y, S, Cout);
 input [n-1:0] X, Y;// Two 4-bit inputs
 output [n-1:0] S;
 output Cout;
 wire [0:n-2] wx;
 //wire w1, w2, w3;

    genvar i;
     FullAdder u1(X[0], Y[0], 1'b0, S[0], wx[0]);
    generate
       for (i=1; i <n-1; i=i+1)
       begin: adder
         FullAdder u1(X[i], Y[i],wx[i-1] , S[i], wx[i]);
       end
    endgenerate
    FullAdder u4(X[n-1], Y[n-1], wx[n-2], S[n-1], Cout);

endmodule



module FullAdder( 
  input X, Y, Ci, output S, Co);
  wire w1,w2,w3;
  //Structural code for one bit full adder
  xor G1(w1, X, Y);
  xor G2(S, w1, Ci);
  and G3(w2, w1, Ci);
  and G4(w3, X, Y);
  or G5(Co, w2, w3);
endmodule



module single_memory(input clk, input MemRead, input[2:0] func3 ,input MemWrite,
 input [7:0] addr, input [31:0] data_in, output [31:0] memory_out);
 
 //reg [7:0] mem [0:256];  to use the 8 - bit address
 reg [7:0] mem [0:256];
 wire[7:0] offset = addr+200;

 reg [31:0] data_out, inst_out;
always @(posedge clk)
 begin
  if(MemWrite == 1'b1)
  begin
 
   case (func3)
     3'b000: mem[offset]<=data_in[7:0]; // SB
     3'b001: {mem[offset+1],mem[offset]}<=data_in[15:0]; // SH
     3'b010: {mem[offset+3],mem[offset+2],mem[offset+1],mem[offset]} <=data_in; // SW
   endcase
  
  end
 end
 
 always @(*)
    begin
   if(MemRead == 1'b1)
   begin
   case (func3)
   3'b000: data_out<={{24{mem[offset][7]}},mem[offset]}; //LB
   3'b001: data_out<={{16{mem[offset+1][7]}},mem[offset+1],mem[offset]}; //LH
   3'b010: data_out<={mem[offset+3],mem[offset+2],mem[offset+1],mem[offset]}; //LW
   3'b100: data_out<={24'd0,mem[offset]}; //LBU: LB but zero extended instead
   3'b101: data_out<={16'd0,mem[offset+1],mem[offset]}; //LHU:LH but zero extended instead
   default:data_out=0;
   endcase
     end
 end

initial begin 
   /* {mem[203],mem[202],mem[201],mem[200]}=32'd17; 
    {mem[207],mem[206],mem[205],mem[204]}=32'd9; 
    {mem[211],mem[210],mem[209],mem[208]}=32'd25; */
    
    
  {mem[3],mem[2],mem[1],mem[0]}=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
  {mem[7],mem[6],mem[5],mem[4]}=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
  {mem[11],mem[10],mem[9],mem[8]}=32'b0000000_00000_00000_000_00000_0110011 ; //add x0, x0, x0
  {mem[15],mem[14],mem[13],mem[12]}=32'h00014417;                //auipc x8,20
  {mem[19],mem[18],mem[17],mem[16]}=32'h00802023;                 //sw x8,12(x0)
  {mem[23],mem[22],mem[21],mem[20]}=32'h00002383;                 //lw x7,12(x0)
  {mem[27],mem[26],mem[25],mem[24]}=32'h0000f4b7;                //LUI x9,15
  {mem[31],mem[30],mem[29],mem[28]}=32'h00849463;               //    bne x9 x8 8
  {mem[35],mem[34],mem[33],mem[32]}=32'h00448493;                  //addi x9 x9 4
  {mem[39],mem[38],mem[37],mem[36]}=32'h00400893;              //addi x17 x0 4
  {mem[43],mem[42],mem[41],mem[40]}=32'h25800513;           //addi x10 x0 600
  {mem[47],mem[46],mem[45],mem[44]}=32'h00750023;      //sb x7 0(x10)
  {mem[51],mem[50],mem[49],mem[48]}=32'h00050103;      //lb x2 0(x10)
  {mem[55],mem[54],mem[53],mem[52]}=32'h00751223;        //    sh x7 4(x10)
  {mem[59],mem[58],mem[57],mem[56]}=32'h00451103;        //lh x2 4(x10)
  {mem[63],mem[62],mem[61],mem[60]}=32'hf6c00593;         //addi x11 x0 -148
  {mem[67],mem[66],mem[65],mem[64]}=32'h0115e463;           //bltu x11 x14 8
  {mem[71],mem[70],mem[69],mem[68]}=32'h00500193;           //addi x3 x0 5
  {mem[75],mem[74],mem[73],mem[72]}=32'h00f00193;           //addi x3 x0 15
  {mem[79],mem[78],mem[77],mem[76]}=32'haf800613;         //addi x12 x0 -1288
  {mem[83],mem[82],mem[81],mem[80]}=32'h00c02423;         //sw x12 8(x0)                                           
  {mem[87],mem[86],mem[85],mem[84]}=32'h00804183;         //lbu x3 8(x0)
  {mem[91],mem[90],mem[89],mem[88]}=32'h00805283;         //lhu x5 8(x0)*/
  {mem[95],mem[94],mem[93],mem[92]}=32'h0051c213;            //xori x4 x3 5
  {mem[99],mem[98],mem[97],mem[96]}=32'h0111c333;         //xor x6 x3 x17
  {mem[103],mem[102],mem[101],mem[100]}=32'h00a1e213;            //ori x4 x3 10
  {mem[107],mem[106],mem[105],mem[104]}=32'h00c1e333;            //or x6 x3 x12
  {mem[111],mem[110],mem[109],mem[108]}=32'h00c37313;         //andi x6 x6 12
  {mem[115],mem[114],mem[113],mem[112]}= 32'h011316b3;         //sll x13 x6 x17
  {mem[119],mem[118],mem[117],mem[116]}= 32'h0116d733;        //srl x14 x13 x17
  {mem[123],mem[122],mem[121],mem[120]}= 32'h4116d7b3;         //sra x15 x13 x17
  {mem[127],mem[126],mem[125],mem[124]}=  32'h00a5a693;         //slti x13 x11 10
  {mem[131],mem[130],mem[129],mem[128]}=32'h00100073 ;   //ebreak
  {mem[135],mem[134],mem[133],mem[132]}=  32'h00a5b713;         //sltiu x14 x11 10
  {mem[139],mem[138],mem[137],mem[136]}=  32'h0115a833;         //slt x16 x11 x17
  {mem[143],mem[142],mem[141],mem[140]}= 32'h0115b7b3;          //sltu x15 x11 x17
//   32'h00000073 //ecall
//   32'h00100073    //ebreak
//    32'h0000000f    //fence

//{mem[127],mem[126],mem[125],mem[124]}
end
 always@(*)
    begin
        inst_out={mem[addr+3],mem[addr+2],mem[addr+1],mem[addr]};
    end

   assign memory_out=(clk)?inst_out:data_out;

endmodule





module ALU_contol_unit(input [2:0] ALUOp, input [2:0] Inst_1, input Inst_2, output reg [3:0] alu_ctr_out );

wire [3:0] alu_ctr;
assign alu_ctr={Inst_1,Inst_2};

always@(*)

 begin
    case (ALUOp)


    3'b000:  // OPCODE_Branch   5'b11_000
    begin 
     alu_ctr_out= `ALU_SUB;
    end
 3'b001:  // OPCODE_Load     5'b00_000
   begin 
    alu_ctr_out= `ALU_ADD;
   end
 3'b010:  // OPCODE_Store    5'b01_000
    begin 
    alu_ctr_out= `ALU_ADD;
   end
 3'b011:// OPCODE_Arith_R  5'b01_100
    begin 
        case(alu_ctr)
               4'b0000  : begin                    //add
                      alu_ctr_out=`ALU_ADD;
                         end
               4'b0001 : begin                    //sub
                    alu_ctr_out= `ALU_SUB;
                         end
               4'b1100  : begin                    //or
                   alu_ctr_out= `ALU_OR   ;
                        end
               4'b1110  : begin                    //and
                  alu_ctr_out=  `ALU_AND    ;
                     end
               4'b1000  : begin                    //xor
                   alu_ctr_out= `ALU_XOR   ;
                         end 
               4'b0010: begin 
                  alu_ctr_out= `ALU_SLL;
               end
              4'b1010: begin
                  alu_ctr_out= `ALU_SRL;     //srli srl
              end
              4'b1011: begin
                    alu_ctr_out=`ALU_SRA ;  //srai   sra    
              end 
              4'b0100: begin
                  alu_ctr_out= `ALU_SLT ;     //slt
              end
              4'b0110: begin
                    alu_ctr_out=`ALU_SLTU  ;  //sltu 
              end 
                default: begin
                      alu_ctr_out= 4'd0;
                      end
         endcase
     end

 3'b101:    //  OPCODE_AUIPC   OPCODE_JALR  5'b01_101
     begin 
        alu_ctr_out = `ALU_ADD ;
    end
  3'b110:  // I    5'b11_001
  begin
     case(Inst_1)
                   3'b000  : begin                    //addi
                        alu_ctr_out=`ALU_ADD;
                           end
                  3'b110  : begin                    //ori
                     alu_ctr_out= `ALU_OR   ;
                          end
                  3'b111  : begin                    //andi
                    alu_ctr_out=  `ALU_AND    ;
                       end
                  3'b100  : begin                    //xori
                     alu_ctr_out= `ALU_XOR   ;
                           end    
                    3'b001: begin 
                       alu_ctr_out= `ALU_SLL;
                           end
                     3'b101: begin
                         alu_ctr_out= `ALU_SRL;     //srli srl
                          end
                     3'b101: begin
                          alu_ctr_out=`ALU_SRA ;  //srai   sra    
                        end    
                    3'b010: begin
                            alu_ctr_out= `ALU_SLT ;     //slt
                             end
                   3'b011: begin
                             alu_ctr_out=`ALU_SLTU  ;  //sltu
                           end 
                   default: begin
                    alu_ctr_out= 4'd0; 
                        end
           endcase
      end
    3'b111:  // OPCODE_LUI 
    begin 
            alu_ctr_out = `ALU_PASS ;
    end
   default: begin
    alu_ctr_out=4'd0;
    end
 endcase
 end

endmodule








module control_unit(input [4:0] instruction, 
output reg auipc_signal, Branch, MemRead, 
output reg [1:0] MemtoReg, 
output reg [2:0] ALUOp,
output reg MemWrite, ALUSrc, RegWrite, halt,
output reg Pc_mux,j_sel
 );
 
 
 always@(*)
 begin
    case (instruction)
    
    `OPCODE_Branch: begin 
        {auipc_signal,Branch, MemRead ,MemtoReg, ALUOp, MemWrite,ALUSrc ,RegWrite,halt,Pc_mux,j_sel}=  14'b01_0_00_000_0_0_0_0_0_0;
        end
    `OPCODE_Load:  begin 
               {auipc_signal,Branch, MemRead ,MemtoReg, ALUOp, MemWrite,ALUSrc ,RegWrite,halt,Pc_mux,j_sel}=  14'b00_1_01_001_0_1_1_0_0_0;
            end
    `OPCODE_Store :  begin 
               {auipc_signal,Branch, MemRead ,MemtoReg, ALUOp, MemWrite,ALUSrc ,RegWrite,halt,Pc_mux,j_sel}=  14'b00_0_0_0_010_1_1_0_0_0_0;
            end
    `OPCODE_JALR :  begin 
                {auipc_signal,Branch, MemRead ,MemtoReg, ALUOp, MemWrite,ALUSrc ,RegWrite,halt,Pc_mux,j_sel}=  14'b00_0_10_101_0_0_1_0_1_0;
            end 
    `OPCODE_JAL  :   begin 
         {auipc_signal,Branch, MemRead ,MemtoReg, ALUOp, MemWrite,ALUSrc ,RegWrite,halt,Pc_mux,j_sel}=  14'b00_0_10_000_0_0_1_0_1_1;
            end  
    `OPCODE_Arith_I: begin 
            {auipc_signal,Branch, MemRead ,MemtoReg, ALUOp, MemWrite,ALUSrc ,RegWrite,halt,Pc_mux,j_sel}=  14'b00_0_00_110_0_1_1_0_0_0;
            end
    `OPCODE_Arith_R:  begin 
       {auipc_signal,Branch, MemRead ,MemtoReg, ALUOp, MemWrite,ALUSrc ,RegWrite,halt,Pc_mux,j_sel}=  14'b00_0_00_011_0_0_1_0_0_0;
            end
    `OPCODE_AUIPC:  begin 
      {auipc_signal,Branch, MemRead ,MemtoReg, ALUOp, MemWrite,ALUSrc ,RegWrite,halt,Pc_mux,j_sel}=  14'b10_0_11_101_0_1_1_0_0_0;
            end
    `OPCODE_LUI:  begin
    {auipc_signal,Branch, MemRead ,MemtoReg, ALUOp, MemWrite,ALUSrc ,RegWrite,halt,Pc_mux,j_sel}=  14'b00_0_11_111_0_1_1_0_0_0;
            end     
    `OPCODE_SYSTEM:  begin //not done
      {auipc_signal,Branch, MemRead ,MemtoReg, ALUOp, MemWrite,ALUSrc ,RegWrite,halt,Pc_mux,j_sel}=  14'd00_0_0_000_0_0_1_0_0;
            end
    `OPCODE_Custom:  begin //not done
            {auipc_signal,Branch, MemRead ,MemtoReg, ALUOp, MemWrite,ALUSrc ,RegWrite,halt,Pc_mux,j_sel}=  14'b00_0_0_000_0_0_0_0_0;
            end
    endcase
 
 end

endmodule





module Branch_CU( input zf, cf, of, sf, input [2:0] func3, output reg flag);



always @(*)
begin

case (func3)
     3'b000: flag = zf; // BEQ
     3'b001: flag = ~zf; // BNE
     3'b100: begin  //BLT
         if(sf != of) begin
           flag = 1;
          end
         else 
          begin
              flag =0;
              end
        end 
     3'b101:  begin //BGE
                 if(sf == of) begin
                   flag = 1;
                  end
                 else 
                  begin
                      flag =0;
                      end
                end               
     3'b110:  flag = ~cf;// BLTU
     3'b111: flag = cf;  // BGEU
     
  
endcase

   end 
endmodule

















//module RiscV_SSD(input clk, rst, SSD_clk,input [1:0] ledSel,input [3:0] ssdSel, output [3:0] Anode,
// output [6:0] LED_out,output [15:0]leds);
//wire [12:0] ssd;
//RISC_V u1 ( clk, rst, SSD_clk, ledSel, ssdSel,  leds, ssd);
//Four_Digit_Seven_Segment_Driver t1 (SSD_clk, ssd, Anode, LED_out);

//endmodule

module HazardDetUnit(input [4:0] read_reg_first,
read_reg_second,ID_EX_Rd, input ID_EX_MemRead, 
output reg stall);
    
    always@(*)
        begin
         stall=0;
            if (((read_reg_first==ID_EX_Rd) || (read_reg_second==ID_EX_Rd))&& ID_EX_MemRead && (ID_EX_Rd!=5'b00000))
                    stall = 1 ;
        end


endmodule


module Forwarding_Unit(input [4:0] ID_EX_Rs1, ID_EX_Rs2, EX_MEM_Rd, MEM_WB_Rd, 
input EX_MEM_RegWrite, MEM_WB_RegWrite, output reg [1:0] forwardA, forwardB);

always@ (*)
begin 

if(EX_MEM_Rd == ID_EX_Rs1 &&( EX_MEM_Rd !=5'b00000) && EX_MEM_RegWrite)
begin
forwardA = 2'b10;
end
 
 else if(MEM_WB_RegWrite && (MEM_WB_Rd !=5'b00000) && MEM_WB_Rd == ID_EX_Rs1) 
begin
 forwardA = 2'b01;
 end 
 else  
  forwardA = 2'b00;
 
if(EX_MEM_RegWrite && (EX_MEM_Rd !=5'b00000) && EX_MEM_Rd == ID_EX_Rs2)
begin
forwardB = 2'b10;
end
  
 else if(MEM_WB_RegWrite && (MEM_WB_Rd !=5'b00000) && MEM_WB_Rd == ID_EX_Rs2)
 begin 
  forwardB = 2'b01;
  
  end
   
else  
   forwardB = 2'b00;
       
 end
endmodule


module mux_4_1 #(parameter n=32)(input [n-1:0] x, y,z,w, input [1:0] sel,output[n-1:0] out );

     assign out= sel[1]?(sel[0]? w:z):(sel[0]? y:x);

endmodule

module signed_seven_segment(input overflow, input clk,
 input [7:0] num,
 output reg [3:0] Anode,
 output reg [6:0] LED_out
 );
 
reg [3:0] LED_BCD;
//wire [3:0] TH;
wire [3:0] Hundreds;
wire [3:0] Tens;
wire [3:0] Ones ;
reg [19:0] refresh_counter = 0; // 20-bit counter\

wire [3:0] sign;
wire [3:0] off;
wire [3:0] e;
wire [3:0] r;


assign sign = 4'b1010;
assign off = 4'b1011;
assign e=  4'b1100;
assign r=  4'b1101;

 wire [1:0] LED_activating_counter;
  always @(posedge clk)
  begin
  refresh_counter <= refresh_counter + 1;
  end
 
  assign LED_activating_counter = refresh_counter[19:18];
 //chwck for the sign and 2's
 reg [7:0] temp;
  always@(*)
 begin
 if (num[7] !=0 )  temp=(~num)+1 ;
 else 
 temp = num;
end
 BCD u1( temp , Hundreds , Tens , Ones);
 
 
  always @(*)
  begin
  case(LED_activating_counter)
  2'b00: begin
  Anode = 4'b0111;
  
  if (num[7] ==0)
  LED_BCD = off ;
  else
  LED_BCD =sign  ;
  end
  2'b01: begin
  Anode = 4'b1011;
  LED_BCD = Hundreds;
  end
  2'b10: begin
  Anode = 4'b1101;
  LED_BCD = Tens;
  end
  2'b11: begin
  Anode = 4'b1110;
  LED_BCD = Ones;
  end
  endcase
  
  if(overflow)
  begin 
  case(LED_activating_counter)
    2'b00: begin
    Anode = 4'b0111;
    LED_BCD = off ;
    end
    2'b01: begin
    Anode = 4'b1011;
    LED_BCD = e;
    end
    2'b10: begin
    Anode = 4'b1101;
    LED_BCD = r;
    end
    2'b11: begin
    Anode = 4'b1110;
    LED_BCD = r;
    end
    endcase
  end
  

  end
  always @(*)
  begin
  case(LED_BCD)
  4'b0000: LED_out = 7'b0000001; // "0"
  4'b0001: LED_out = 7'b1001111; // "1"
  4'b0010: LED_out = 7'b0010010; // "2"
  4'b0011: LED_out = 7'b0000110; // "3"
  4'b0100: LED_out = 7'b1001100; // "4"
  4'b0101: LED_out = 7'b0100100; // "5"
  4'b0110: LED_out = 7'b0100000; // "6"
  4'b0111: LED_out = 7'b0001111; // "7"
  4'b1000: LED_out = 7'b0000000; // "8"
  4'b1001: LED_out = 7'b0000100; // "9"
  4'b1010: LED_out = 7'b1111110; // "-"
  4'b1011: LED_out = 7'b1111111; // "off"
  4'b1100: LED_out = 7'b0010000; // "E"
  4'b1101: LED_out = 7'b1111010; // "r"
  default: LED_out = 7'b0000001; // "0"
  endcase
  end
 endmodule 

module BCD (
    input [7:0] num,
   // output reg [3:0] Thousands,
    output reg [3:0] Hundreds,
    output reg [3:0] Tens,
    output reg [3:0] Ones 
    );
    
 integer i;
 always @(num)
 begin
        //initialization 
   // Thousands = 4'd0; 
    Hundreds = 4'd0; 
    Tens = 4'd0;  
    Ones = 4'd0;
    for (i = 7; i >= 0 ; i = i-1 ) 
    begin 
      //  if(Thousands >= 5 )  
  //  Thousands = Thousands + 3;
    if(Hundreds >= 5 )  
    Hundreds = Hundreds + 3; 
    if (Tens >= 5 )
       Tens = Tens + 3;  
    if (Ones >= 5)
        Ones = Ones +3; 

 //shift left one 
 //Thousands = Thousands << 1;
// Thousands [0] = Hundreds [3];
 Hundreds = Hundreds << 1; 
 Hundreds [0] = Tens [3]; 
 Tens = Tens << 1; 
 Tens [0] = Ones[3]; 
 Ones = Ones << 1;
  Ones[0] = num[i];
 end 

end endmodule




module Four_Digit_Seven_Segment_Driver (
 input clk,
 input [12:0] num,
 output reg [3:0] Anode,
 output reg [6:0] LED_out
 );

 reg [3:0] LED_BCD;
 reg [19:0] refresh_counter = 0; // 20-bit counter
 wire [1:0] LED_activating_counter;
 always @(posedge clk)
 begin
 refresh_counter <= refresh_counter + 1;
 end

 assign LED_activating_counter = refresh_counter[19:18];

 always @(*)
 begin
 case(LED_activating_counter)
 2'b00: begin
 Anode = 4'b0111;
 LED_BCD = num/1000;
 end
 2'b01: begin
 Anode = 4'b1011;
 LED_BCD = (num % 1000)/100;
 end
 2'b10: begin
 Anode = 4'b1101;
 LED_BCD = ((num % 1000)%100)/10;
 end
 2'b11: begin
 Anode = 4'b1110;
 LED_BCD = ((num % 1000)%100)%10;
 end
 endcase
 end
 always @(*)
 begin
 case(LED_BCD)
 4'b0000: LED_out = 7'b0000001; // "0"
 4'b0001: LED_out = 7'b1001111; // "1"
 4'b0010: LED_out = 7'b0010010; // "2"
 4'b0011: LED_out = 7'b0000110; // "3"
 4'b0100: LED_out = 7'b1001100; // "4"
 4'b0101: LED_out = 7'b0100100; // "5"
 4'b0110: LED_out = 7'b0100000; // "6"
 4'b0111: LED_out = 7'b0001111; // "7"
 4'b1000: LED_out = 7'b0000000; // "8"
 4'b1001: LED_out = 7'b0000100; // "9"
 default: LED_out = 7'b0000001; // "0"
 endcase
 end
endmodule 


















