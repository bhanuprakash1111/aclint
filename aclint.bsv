package aclint;

import ConfigReg::*;
import ConcatReg :: * ;
import axi4l::*;
import axi4::*;
import apb::*;
import DCBus::*;
import BUtils ::*;
import GetPut::*;
import Assert::*;
import DefaultValue::*;
import Reserved :: * ;
  
export Ifc_clint_axi4l    (..);
export Ifc_clint_apb      (..);
export Ifc_clint_sb       (..);
export mkclint_axi4l;
export mkclint_apb;
export mk_clint_block;

typedef IWithSlave#(Ifc_apb_slave#(aw, dw, uw), Ifc_clint_sb#(tick_count, msip_size, num_int))
      Ifc_clint_apb#(type aw, type dw, type uw, numeric type tick_count, numeric type msip_size, numeric type num_int);
      
typedef IWithSlave#(Ifc_axi4l_slave#(aw, dw, uw), Ifc_clint_sb#(tick_count, msip_size, num_int))
      Ifc_clint_axi4l#(type aw, type dw, type uw, numeric type tick_count, numeric type msip_size, numeric type num_int);

/*typedef IWithSlave#(Ifc_axi4_slave#(iw, aw, dw, uw), Ifc_clint_sb#(tick_count, msip_size, num_int))
      Ifc_clint_axi4#(type iw, type aw, type dw, type uw, numeric type tick_count, numeric type msip_size, numeric type num_int);*/

typedef struct{
    ReservedZero#(TSub#(32,m)) zeros;
   Bit#(m) msip;
  } MsipReg#(numeric type m) deriving (Bits, Eq, FShow);


interface Ifc_clint_sb#(numeric type tick_count, numeric type msip_size, numeric type num_int );
    (*always_ready*)
    method Array#(Bit#(1)) sb_clint_msip;
    (*always_ready*)
    method Array#(Bit#(1)) sb_clint_mtip;
    (*always_ready*)
    method Bit#(64) sb_clint_mtime;
endinterface

  
module [ModWithDCBus#(aw,dw)] mk_clint(Ifc_clint_sb#( tick_count, msip_size, num_int))
	provisos(
	Log#(tick_count, tick_count_bits),
      	Add#(16, _a, aw),
      	Add#(8, _b, dw),         // data atleast 8 bits
      	Mul#(TDiv#(dw,8),8, dw), // dw is a proper multiple of 8 bits
      	Add#(d__, 3, aw),
	Add#(a__, 2, aw),
      	Add#(dw, c__, 64),
      	Add#(TExp#(TLog#(dw)),0,dw),
      	Add#(b__, TDiv#(dw, 8), 8),
      	Mul#(TDiv#(TAdd#(TSub#(64, msip_size), msip_size), 8), 8, TAdd#(TSub#(64,
    	msip_size), msip_size)),
    	Mul#(TDiv#(TAdd#(TSub#(64, num_int), num_int), 8), 8, TAdd#(TSub#(64,
    	num_int), num_int))
		);	
		
staticAssert(valueOf(TExp#(tick_count_bits))==valueOf(tick_count),"tick count not a power of 2");

Integer numint = valueof(num_int);
Integer msip_num = valueof(msip_size);
Array#(DCRAddr#(aw,3)) attr_msip;
for(Integer i=0;i<(msip_num);i=i+1)
	begin
	Bit#(aw) j= fromInteger(i);
	attr_msip[i]     = DCRAddr{addr:'h0000+j*'h0004, min: Sz1, max:Sz8, mask:3'b100}; 
	end
Array#(DCRAddr#(aw,3)) attr_mtimecmp;
for(Integer i=0;i<(numint);i=i+1)
	begin
	Bit#(aw) j= fromInteger(i);
 	attr_mtimecmp[i] = (DCRAddr{addr:('h0000+j*'h0008), min: Sz1, max:Sz8, mask:3'b111}); 
    	end
    		
DCRAddr#(aw,3) attr_mtime    = DCRAddr{addr:'hbff8, min: Sz1, max:Sz8, mask:3'b111};
    
Array#(Reg#(Bit#(1))) rg_mtip;
for(Integer i=0;i<(numint);i=i+1)
	begin
	rg_mtip[i]          <- mkReg(0);
	end
		
Reg#(Bit#(tick_count_bits)) rg_tick          <- mkReg(0);
Array#(Reg#(MsipReg#(1)) )  rg_msip;
for(Integer i=0;i<(msip_num);i=i+1)
	begin
	rg_msip[i]     <- mkDCBRegRW(attr_msip[i], unpack(0));
	end
Array#(Reg#(Bit#(64))) rg_mtimecmp;	
for(Integer i=0;i<(numint);i=i+1)
	begin
	rg_mtimecmp[i] <- mkDCBRegRWSe(attr_mtimecmp[i],  '1, rg_mtip[i]._write(0));
	end
		
Reg#(Bit#(64))              rg_mtime    <- mkDCBRegRW(attr_mtime, 'h0);


rule rl_generate_interrupt;
		
for(Integer i=0;i<(numint);i=i+1)
	begin
	rg_mtip[i]<=pack(rg_mtime >= rg_mtimecmp[i]); 
	end
endrule:rl_generate_interrupt

rule rl_increment_timer;
if(rg_tick == 0)begin
	rg_mtime <= rg_mtime + 1;
end
rg_tick <= rg_tick + 1;
endrule:rl_increment_timer

   
method sb_clint_msip;
Array#(Bit#(1)) sb_clint_msipx;
for(Integer i=0;i<(msip_num);i=i+1)
	begin
	sb_clint_msipx[i]= rg_msip[i].msip;
	end
	return sb_clint_msipx;
endmethod
  
method sb_clint_mtip;
Array#(Bit#(1)) sb_clint_mtipx;
for(Integer i=0;i<(numint);i=i+1)
	begin
	sb_clint_mtipx[i]= rg_mtip[i];
	end
	return sb_clint_mtipx;
endmethod
method sb_clint_mtime = rg_mtime;

endmodule:mk_clint
  
   module [Module] mk_clint_block
    (IWithDCBus#(DCBus#(aw,dw), Ifc_clint_sb#(tick_count, msip_size, num_int)))
		provisos(
		  Log#(tick_count, tick_count_bits),
      Add#(16, _a, aw),
      Add#(8, _b, dw),         // data atleast 8 bits
      Mul#(TDiv#(dw,8),8, dw), // dw is a proper multiple of 8 bits
      Add#(d__, 3, aw),

      Add#(a__, 2, aw),
      Add#(dw, c__, 64),
      Add#(TExp#(TLog#(dw)),0,dw),
      Add#(b__, TDiv#(dw, 8), 8),
      Mul#(TDiv#(TAdd#(TSub#(64, msip_size), msip_size), 8), 8, TAdd#(TSub#(64,
    msip_size), msip_size)),
    Mul#(TDiv#(TAdd#(TSub#(64, num_int), num_int), 8), 8, TAdd#(TSub#(64,
    	num_int), num_int))
		);	
    let ifc <- exposeDCBusIFC(mk_clint);
    return ifc;
  endmodule:mk_clint_block

module [Module] mkclint_apb#(parameter Integer base, Clock clint_clk, Reset clint_rst)
  (Ifc_clint_apb#(aw, dw, uw, tick_count, msip_size, num_int))
		provisos(
		  Log#(tick_count, tick_count_bits),
      Add#(16, _a, aw),
      Add#(8, _b, dw),         // data atleast 8 bits
      Mul#(TDiv#(dw,8),8, dw), // dw is a proper multiple of 8 bits
      Add#(d__, 3, aw),

      Add#(a__, 2, aw),
      Add#(dw, c__, 64),
      Add#(TExp#(TLog#(dw)),0,dw),
      Add#(b__, TDiv#(dw, 8), 8),
      Mul#(TDiv#(TAdd#(TSub#(64, msip_size), msip_size), 8), 8, TAdd#(TSub#(64,
    msip_size), msip_size)),
    Mul#(TDiv#(TAdd#(TSub#(64, num_int), num_int), 8), 8, TAdd#(TSub#(64,
    	num_int), num_int))
		);	
    
    let clint_mod = mk_clint_block(clocked_by clint_clk, reset_by clint_rst);
    Ifc_clint_apb#(aw, dw, uw, tick_count, msip_size, num_int) clint <-
        dc2apb(clint_mod, base, clint_clk, clint_rst);
    return clint;
  endmodule:mkclint_apb
  
  module [Module] mkclint_axi4l#(parameter Integer base, Clock clint_clk, Reset clint_rst)
    (Ifc_clint_axi4l#(aw, dw, uw, tick_count, msip_size, num_int))
		provisos(
		  Log#(tick_count, tick_count_bits),
      Add#(16, _a, aw),
      Add#(8, _b, dw),         // data atleast 8 bits
      Mul#(TDiv#(dw,8),8, dw), // dw is a proper multiple of 8 bits
      Add#(d__, 3, aw),

      Add#(a__, 2, aw),
      Add#(dw, c__, 64),
      Add#(TExp#(TLog#(dw)),0,dw),
      Add#(b__, TDiv#(dw, 8), 8),
      Mul#(TDiv#(TAdd#(TSub#(64, msip_size), msip_size), 8), 8, TAdd#(TSub#(64,
    msip_size), msip_size)),
    Mul#(TDiv#(TAdd#(TSub#(64, num_int), num_int), 8), 8, TAdd#(TSub#(64,
    	num_int), num_int))
		);	

    let clint_mod = mk_clint_block(clocked_by clint_clk, reset_by clint_rst);
    Ifc_clint_axi4l#(aw, dw, uw, tick_count, msip_size, num_int) clint <-
        dc2axi4l(clint_mod, base, clint_clk, clint_rst);
    return clint;
    
 /*module [Module] mkclint_axi4#(Clock clint_clk, Reset clint_rst)
  (Ifc_clint_axi4#(iw, aw, dw, uw, tick_count, msip_size))
		provisos(
		  Log#(tick_count, tick_count_bits),
      Add#(16, _a, aw),
      Add#(8, _b, dw),         // data atleast 8 bits
      Mul#(TDiv#(dw,8),8, dw), // dw is a proper multiple of 8 bits

      Add#(a__, 2, aw),
      Add#(dw, c__, 64),
      Add#(TExp#(TLog#(dw)),0,dw),
      Add#(b__, TDiv#(dw, 8), 8),
      Mul#(TDiv#(TAdd#(TSub#(64, msip_size), msip_size), 8), 8, TAdd#(TSub#(64,
    msip_size), msip_size))

		);	
    
    let clint_mod = mk_clint_block(clocked_by clint_clk, reset_by clint_rst);
    Ifc_clint_axi4#(iw, aw, dw, uw, tick_count, msip_size) clint <-
        dc2axi4(clint_mod, clint_clk, clint_rst);
    return clint;
  endmodule:mkclint_axi4*/

  endmodule:mkclint_axi4l
  
  

  endpackage:aclint
