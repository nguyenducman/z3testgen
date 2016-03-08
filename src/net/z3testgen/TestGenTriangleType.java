package net.z3testgen;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.Model;
import com.microsoft.z3.Params;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Tactic;
import com.microsoft.z3.Z3Exception;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Collections;
import java.util.ArrayList;

import java.util.Date;
import java.util.List;
class TriangleType1{
    public IntExpr sideA;
    public IntExpr sideB;
    public IntExpr sideC;
    public Expr type;
    
    public TriangleType1(IntExpr sideA, IntExpr sideB, IntExpr sideC,Expr type) {
        this.sideA = sideA;
        this.sideB = sideB;
        this.sideC = sideC;
        this.type=type;
    }
}
public class TestGenTriangleType {


	
	@SuppressWarnings("null")
	public static void main(String[] args) throws Z3Exception, IOException {
		ArrayList<TriangleType1> TestData = new ArrayList<TriangleType1>(); 
		Context ctx = new Context();
		 Tactic smtTactic = ctx.mkTactic("smt");
         
		 Params p = ctx.mkParams();
		 
		 Tactic using = ctx.usingParams(smtTactic, p); //then(simplifyTactic, smtTactic, new Tactic[] {});
		 //Read file SMT2
		 BoolExpr expr = ctx.parseSMTLIB2File("input/Triangle.smt2",null,null,null,null);
		 Solver s = ctx.mkSolver(using);	
		 s.setParameters(p);
		 Model m= null;		
		 
		 Solver si = ctx.mkSolver(using);
		 Solver sr = ctx.mkSolver(using);
		 
		 si.setParameters(p);
		 sr.setParameters(p);
		 

		 // Declare side a,b,c 
		 IntExpr a;
		 IntExpr b;
		 IntExpr c;
		 IntExpr aa;
		 IntExpr bb;
		 IntExpr cc;
		 IntExpr tong;
		 Expr f;
	 
// range of value
		 int max = Integer.MAX_VALUE;
	// int max = 1000;
		 int min = 0;
		 int lb =1;
	 
// LBound, UBound, UnBound, UpBound, NLBound, NUBound, MidVal
		 IntExpr LBound = ctx.mkInt(lb);
		 IntExpr UBound = ctx.mkInt(max);
		 IntExpr NLBound = (IntExpr)ctx.mkAdd(LBound, ctx.mkInt(1));
		 IntExpr NUBound = (IntExpr)ctx.mkSub(UBound, ctx.mkInt(1));
		 IntExpr UnBound = (IntExpr)ctx.mkSub(LBound, ctx.mkInt(1));

		 IntExpr MidVal = (IntExpr)ctx.mkDiv(ctx.mkAdd(UBound, LBound),ctx.mkInt(2));

		 Date before = new Date();
		 long t_diff = ((new Date()).getTime() - before.getTime());// / 1000;
		 System.out.println("SMT2 file read time: " + t_diff + " sec");
 
//write solution to csv file  
		 FileWriter writer = new FileWriter("output/Triangle2.csv");
		 System.out.println("model for: Triangle Type");
		 writer.append("a");
		 writer.append(',');
		 writer.append("b");
		 writer.append(',');
		 writer.append("c");
		 writer.append(',');
		 writer.append("TType");
		 writer.append('\n');
		 //finding all satisfiable models	 
		 s.add(expr);
		 
		 int i =0;
		 while(s.check() == Status.SATISFIABLE && i <100){
			 i++;
			 
			 p.add("random_seed", i);
			 s.setParameters(p);	

			 m = s.getModel(); // get value and print out

			 a =  ctx.mkIntConst(m.getConstDecls()[1].getName());
			 b =  ctx.mkIntConst(m.getConstDecls()[0].getName());
			 c =  ctx.mkIntConst(m.getConstDecls()[2].getName());
			 
			 //f = //m.getConstDecls()[3].getName();
			 aa= (IntExpr)m.eval(m.getConstInterp(m.getConstDecls()[1]), false);
			 bb= (IntExpr)m.eval(m.getConstInterp(m.getConstDecls()[0]), false);
			 cc= (IntExpr)m.eval(m.getConstInterp(m.getConstDecls()[2]), false);
			 tong = (IntExpr) ctx.mkAdd(aa,bb,cc);
			 f = m.eval(m.getConstInterp(m.getConstDecls()[3]), false);
			 if (Integer.parseInt(aa.toString())== Integer.parseInt(LBound.toString())){
				 writer.append(""+ aa+"(LBound)");
			 } else if (Integer.parseInt(aa.toString())== Integer.parseInt(UBound.toString())){
				 writer.append(""+ aa+"(UBound)");
			 } else
				 writer.append(""+ m.eval(m.getConstInterp(m.getConstDecls()[1]), false));
			 writer.append(',');
			 if (Integer.parseInt(bb.toString())== Integer.parseInt(LBound.toString())){
				 writer.append(""+bb+"(LBound)");
			 } else if (Integer.parseInt(bb.toString())== Integer.parseInt(UBound.toString())){
				 //} else if (bb.toString()==UBound.toString()){
				 writer.append(""+bb+"(UBound)");
			 }else
				 writer.append(""+m.eval(m.getConstInterp(m.getConstDecls()[0]), false));
			 writer.append(',');
			 if (Integer.parseInt(cc.toString())==Integer.parseInt(LBound.toString())){
				 writer.append(""+cc+"(LBound)");
			 }else if (Integer.parseInt(cc.toString())==Integer.parseInt(UBound.toString())){
				 writer.append(""+cc+"(UBound)");
			 }else
				 writer.append(""+m.eval(m.getConstInterp(m.getConstDecls()[2]), false));
			 writer.append(',');
			 writer.append(""+m.eval(m.getConstInterp(m.getConstDecls()[3]), false));
			 writer.append('\n');		
		
			//====================== add to ArrayList================

//			 TestData.add(new TriangleType1(aa,bb,cc,m.eval(m.getConstInterp(m.getConstDecls()[3]), false)));
			 
			 // constraint LBound <= a,b,c <=UBound	 
			 s.add(ctx.mkAnd(ctx.mkAnd(ctx.mkLe(a,UBound),ctx.mkLe(b,UBound),ctx.mkLe(c,UBound)),
					 ctx.mkAnd(ctx.mkGe(a,LBound),ctx.mkGe(b,LBound),ctx.mkGe(c,LBound))));
			 // seek to next model
			 s.add(ctx.mkOr(ctx.mkEq(ctx.mkEq(a, m.eval(m.getConstInterp(m.getConstDecls()[1]), false)), ctx.mkFalse()),
					 ctx.mkEq(ctx.mkEq(b, m.eval(m.getConstInterp(m.getConstDecls()[0]), false)), ctx.mkFalse()),
					 ctx.mkEq(ctx.mkEq(c, m.eval(m.getConstInterp(m.getConstDecls()[2]), false)), ctx.mkFalse()),
					 ctx.mkAnd(ctx.mkEq(ctx.mkEq(tong, ctx.mkAdd(a,b,c)), ctx.mkFalse()),ctx.mkEq(ctx.mkEq(f,m.eval(m.getConstInterp(m.getConstDecls()[3]), false) ),ctx.mkFalse()))
					 ));
			 s.add(ctx.mkOr(ctx.mkAnd(ctx.mkLe(a,NLBound),ctx.mkLe(b,NLBound),ctx.mkLe(c,NLBound)),
					 ctx.mkAnd(ctx.mkGe(a,NUBound),ctx.mkGe(b,NUBound),ctx.mkGe(c,NUBound)),
				//	 ctx.mkAnd(ctx.mkGt(a,NLBound),ctx.mkGt(b,NLBound),ctx.mkGt(c,NLBound)),
					 ctx.mkAnd(ctx.mkEq(a,MidVal),ctx.mkEq(b,MidVal),ctx.mkEq(c,MidVal)),
					 ctx.mkOr(ctx.mkEq(a,MidVal),ctx.mkEq(b,MidVal),ctx.mkEq(c,MidVal))));
				//					 ctx.mkLt(a,NUBound),ctx.mkLt(b,NUBound),ctx.mkLt(c,NUBound))));//,
				//				 ctx.mkAnd(ctx.mkLt(a,NUBound),ctx.mkLt(b,NUBound),ctx.mkLt(c,NUBound))));	
			 
	
	//			 System.out.println(g.getFormulas());
			 //only EQUI
			 //s.add(ctx.mkAnd(ctx.mkEq(a, b),ctx.mkEq(b, c) ));
			 /*
			  * 
			  * ---- only ISO
			 s.add(ctx.mkOr(ctx.mkAnd(ctx.mkEq(a, b),ctx.mkNot(ctx.mkEq(b, c)) ),
					 ctx.mkAnd(ctx.mkEq(b, c),ctx.mkNot(ctx.mkEq(c, a)) ),
					 ctx.mkAnd(ctx.mkEq(a, c),ctx.mkNot(ctx.mkEq(b, c)) )
					 ));
					// */
	 
	
		 }
////check Invalid partition
		 si.add(expr);
		 // m = si.getModel(); // get value and print out
		 a =  ctx.mkIntConst(m.getConstDecls()[1].getName());// get variable name (symbol)
		 b =  ctx.mkIntConst(m.getConstDecls()[0].getName());
		 c =  ctx.mkIntConst(m.getConstDecls()[2].getName());
		 si.add(ctx.mkOr(ctx.mkAnd(ctx.mkGt(a,UBound),ctx.mkGt(b,UBound),ctx.mkGt(c,UBound)),
				 ctx.mkAnd(ctx.mkLt(a,LBound),ctx.mkLt(b,LBound),ctx.mkLt(c,LBound))));	 

		 int j=0;
		 while(si.check() == Status.SATISFIABLE && j< 6){
//			 TriangleType1 TT = new TriangleType1();
			 p.add("random_seed", j);
			 si.setParameters(p);	
			 m = si.getModel(); // get value and print out
			 aa= (IntExpr)m.eval(m.getConstInterp(m.getConstDecls()[1]), false);
			 bb= (IntExpr)m.eval(m.getConstInterp(m.getConstDecls()[0]), false);
			 cc= (IntExpr)m.eval(m.getConstInterp(m.getConstDecls()[2]), false);
			 
//			 TT.sideA = aa;
//			 TT.sideB = bb;
//			 TT.sideC = cc;
//			 TT.type = m.eval(m.getConstInterp(m.getConstDecls()[3]), false);
//			 TestData.add(new TriangleType1(aa,bb,cc,m.eval(m.getConstInterp(m.getConstDecls()[3]), false)));
			 
			 writer.append(""+ aa);
			 writer.append(',');
			 writer.append(""+bb);
			 writer.append(',');
			 writer.append(""+cc);
			 writer.append(',');
			 writer.append("INVALID");
			 writer.append('\n');		
			 
			 //	}
			 // seek to next model  

			 si.add(ctx.mkOr(ctx.mkEq(ctx.mkEq(a, m.eval(m.getConstInterp(m.getConstDecls()[1]), false)), ctx.mkFalse()),
					 ctx.mkEq(ctx.mkEq(b, m.eval(m.getConstInterp(m.getConstDecls()[0]), false)), ctx.mkFalse()),
					 ctx.mkEq(ctx.mkEq(c, m.eval(m.getConstInterp(m.getConstDecls()[2]), false)), ctx.mkFalse())
					 ));
			 j++;
		 }
//		  //Sap xep!
////	        Collections.sort(danhSach, new Comparator<SinhVien>() {
////	            @Override
////	            public int compare(SinhVien sv1, SinhVien sv2) {
////	                if (sv1.diem < sv2.diem) {
////	                    return 1;
////	                } else {
////	                    if (sv1.diem == sv2.diem) {
////	                        return 0;
////	                    } else {
////	                        return -1;
////	                    }
////	                }
////	            }
////	        });
//		 for (int k=0;k<TestData.size();k++){
////			if (){
////						
////			 writer.append(""+TestData.get(k).sideA);
////			 writer.append(',');
////			 writer.append(""+TestData.get(k).sideB);
////			 writer.append(',');
////			 writer.append(""+TestData.get(k).sideC);
////			 writer.append(',');
////			 writer.append(""+TestData.get(k).type);
////			 writer.append('\n');		
//			}	 
//			 writer.append(""+TestData.get(k).sideA);
//			 writer.append(',');
//			 writer.append(""+TestData.get(k).sideB);
//			 writer.append(',');
//			 writer.append(""+TestData.get(k).sideC);
//			 writer.append(',');
//			 writer.append(""+TestData.get(k).type);
//			 writer.append('\n');		
//		 }
		 // Close file
		 long t_diff2 = ((new Date()).getTime() - before.getTime());// / 1000;
		 System.out.println("SMT2 file test took " + t_diff2 + " ms");
		 writer.flush();
		 writer.close();

		 System.out.println("Success!");
	}

}
