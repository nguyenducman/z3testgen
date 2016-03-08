package net.z3testgen;
import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.EnumSort;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.Model;
import com.microsoft.z3.Params;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Symbol;
import com.microsoft.z3.Tactic;
import com.microsoft.z3.Z3Exception;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Date;
public class Z3TestGenTType {

	public static void main(String[] args) throws Z3Exception, IOException {
	
		Context ctx = new Context();
		 Tactic smtTactic = ctx.mkTactic("smt");
		 Params p = ctx.mkParams();
		 p.add("arith.random_initial_value", true);
				 
		 Tactic using = ctx.usingParams(smtTactic, p); //then(simplifyTactic, smtTactic, new Tactic[] {});
		 Solver s = ctx.mkSolver(using);	
		 Solver si = ctx.mkSolver(using);
		 Solver sr = ctx.mkSolver(using);
		 s.setParameters(p);
		 si.setParameters(p);
		 sr.setParameters(p);
		 Model m= null;		

 /* 
 *------------------------------------------ 
 declare : enum TType {EQUI, ISO, SCA, NOT}*/
	 Symbol name = ctx.mkSymbol("TType");
	 EnumSort TType = ctx.mkEnumSort(name, ctx.mkSymbol("EQUI"),
	         ctx.mkSymbol("ISO"), ctx.mkSymbol("SCA"),ctx.mkSymbol("NOT"));
	 
	 Expr EQUI = TType.getConsts()[0];
	 Expr ISO = TType.getConsts()[1];
	 Expr SCA = TType.getConsts()[2];
	 Expr NOT = TType.getConsts()[3];
	 
// Declare side a,b,c 
	 IntExpr a = ctx.mkIntConst("a");
	 IntExpr b = ctx.mkIntConst("b");
	 IntExpr c = ctx.mkIntConst("c");
	 
// range of value
	 int max = Integer.MAX_VALUE;
	// int max = 1000;
	 int min = 0;
	 int lb =1;
	 
//Scope of a,b,c value;	 
	 s.add(ctx.mkGe(a, ctx.mkInt(min)));
	 s.add(ctx.mkGe(b, ctx.mkInt(min)));
	 s.add(ctx.mkGe(c, ctx.mkInt(min)));
	 s.add(ctx.mkLe(a, ctx.mkInt(max)));
	 s.add(ctx.mkLe(b, ctx.mkInt(max)));
	 s.add(ctx.mkLe(c, ctx.mkInt(max)));
// LBound, UBound, UnBound, UpBound, NLBound, NUBound, MidVal
	 IntExpr LBound = ctx.mkInt(lb);
	 IntExpr UBound = ctx.mkInt(max);
	 IntExpr NLBound = (IntExpr)ctx.mkAdd(LBound, ctx.mkInt(1));
	 IntExpr NUBound = (IntExpr)ctx.mkSub(UBound, ctx.mkInt(1));
	 IntExpr UnBound = (IntExpr)ctx.mkSub(LBound, ctx.mkInt(1));
//	 
	 IntExpr MidVal = (IntExpr)ctx.mkDiv(ctx.mkAdd(UBound, LBound),ctx.mkInt(2));


//define boolean condition expression
	 BoolExpr eq_ab = ctx.mkEq(a, b); //a==b
	 BoolExpr eq_bc = ctx.mkEq(b, c); //b==c
	 BoolExpr eq_ca = ctx.mkEq(c, a); //c==a
	 IntExpr abc = (IntExpr) ctx.mkAdd(ctx.mkAdd(a,b),c);
	 BoolExpr tri1 = ctx.mkGt(ctx.mkAdd(a,b),c); // a+b>c
	 BoolExpr tri2 = ctx.mkGt(ctx.mkAdd(b,c),a); //b+c >a
	 BoolExpr tri3 = ctx.mkGt(ctx.mkAdd(c,a),b); // c+a >b
	 BoolExpr tri = ctx.mkAnd(tri1,tri2,tri3); //is triangle
	 //sides less than 0
	 BoolExpr side_le0 = ctx.mkOr(ctx.mkLe(a,ctx.mkInt(0)),ctx.mkLe(b,ctx.mkInt(0)),ctx.mkLe(c,ctx.mkInt(0)));
	 
	 //pre-condition a,b,c >0
	 BoolExpr side_gt0 =ctx.mkAnd(ctx.mkGt(a, ctx.mkInt(0)),ctx.mkGt(b, ctx.mkInt(0)),ctx.mkGt(c, ctx.mkInt(0)));
	 BoolExpr side_gtx =ctx.mkAnd(ctx.mkGt(a, ctx.mkInt(10)),ctx.mkGt(b, ctx.mkInt(10)),ctx.mkGt(c, ctx.mkInt(10)));
//Check type of Triangle in part
	 // Check valid type or not, and what type of Triangle
	 BoolExpr CheckSCA = ctx.mkAnd(side_gt0,tri, ctx.mkNot(eq_ab), ctx.mkNot(eq_bc), ctx.mkNot(eq_ca));
	 BoolExpr CheckEQUI = ctx.mkAnd(side_gt0,tri, eq_ab, eq_bc);
	 BoolExpr CheckISO= ctx.mkOr(ctx.mkAnd(side_gt0,tri, eq_ab, ctx.mkNot(eq_bc)),ctx.mkAnd(side_gt0,tri, eq_bc, ctx.mkNot(eq_ca)),ctx.mkAnd(side_gt0,tri, eq_ca, ctx.mkNot(eq_ab)));
	 BoolExpr CheckNOT = ctx.mkAnd(ctx.mkNot(tri),side_gt0);
	 
	 BoolExpr CheckInvalid = ctx.mkOr(ctx.mkLt(a,LBound),ctx.mkLt(b,LBound),ctx.mkLt(c,LBound),ctx.mkGt(a,UBound),ctx.mkGt(b,UBound),ctx.mkGt(c,UBound),
			 		ctx.mkAnd(ctx.mkLt(a,LBound),ctx.mkLt(b,LBound),ctx.mkLt(c,LBound)), ctx.mkAnd(ctx.mkGt(a,UBound),ctx.mkGt(b,UBound),ctx.mkGt(c,UBound)));
	 //BoolExpr CheckInvalid = ctx.mkOr(side_le0,ctx.mkGt(a,UBound),ctx.mkGt(b,UBound),ctx.mkGt(c,UBound));
	 
	 BoolExpr Checka_eq_bc = ctx.mkOr(ctx.mkNot(tri), ctx.mkEq(a, ctx.mkAdd(b,c)));//a==b+c
	 BoolExpr Checkb_eq_ca = ctx.mkOr(ctx.mkNot(tri), ctx.mkEq(b, ctx.mkAdd(a,c)));//b==a+c
	 BoolExpr Checkc_eq_ab = ctx.mkOr(ctx.mkNot(tri), ctx.mkEq(c, ctx.mkAdd(b,a)));//c==b+a
	 BoolExpr Checka_gt_bc = ctx.mkOr(ctx.mkNot(tri), ctx.mkGt(a, ctx.mkAdd(b,c)));//a > b+c
	 BoolExpr Checkb_gt_ca = ctx.mkOr(ctx.mkNot(tri), ctx.mkGt(b, ctx.mkAdd(a,c)));//b > a+c
	 BoolExpr Checkc_gt_ab = ctx.mkOr(ctx.mkNot(tri), ctx.mkGt(c, ctx.mkAdd(b,a)));//c > b+a

	 //=====================================================	 
//assert constraints to find models
	 Expr tg = ctx.mkITE(CheckEQUI, EQUI, ctx.mkITE(CheckISO, ISO, ctx.mkITE(CheckSCA, SCA,NOT)));
	 BoolExpr tgiac =ctx.mkOr(ctx.mkEq(SCA,tg),ctx.mkEq(EQUI,tg),ctx.mkEq(ISO,tg),ctx.mkEq(NOT,tg));
	//s.add(tgiac);;
	//s.add(ctx.mkOr(CheckEQUI,CheckISO,CheckSCA,CheckNOT));
	 Date before = new Date();
	 long t_diff = ((new Date()).getTime() - before.getTime());// / 1000;
     System.out.println("SMT2 file read time: " + t_diff + " sec");
     
     
	 s.add(ctx.mkOr(CheckEQUI,CheckISO,CheckSCA,CheckNOT));
	// s.add(ctx.mkOr(Checka_eq_bc,Checkb_eq_ca,Checkc_eq_ab));
//write solution to csv file  
	 FileWriter writer = new FileWriter("data/Triangle.csv");
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
	 int i =1;
     while(s.check() == Status.SATISFIABLE && i <51){
		 p.add("random_seed", i);
		 s.setParameters(p);	
    	m = s.getModel(); // get value and print out
		if (Integer.parseInt(m.eval(a,false).toString())==Integer.parseInt(LBound.toString())){
			writer.append(""+ m.eval(a,false)+"(LBound)");
		}else if (Integer.parseInt(m.eval(a,false).toString())==Integer.parseInt(UBound.toString())){
			writer.append(""+ m.eval(a,false)+"(UBound)");
		} else
			writer.append(""+ m.eval(a,false));
		writer.append(',');
		if (Integer.parseInt(m.eval(b,false).toString())==Integer.parseInt(LBound.toString())){
			 writer.append(""+m.eval(b,false)+"(LBound)");
		} else if (Integer.parseInt(m.eval(b,false).toString())==Integer.parseInt(UBound.toString())){
			 writer.append(""+m.eval(b,false)+"(UBound)");
		}else
			 writer.append(""+m.eval(b,false));
		writer.append(',');
		if (Integer.parseInt(m.eval(c,false).toString())==Integer.parseInt(LBound.toString())){
			 writer.append(""+m.eval(c,false)+"(LBound)");
		}else if (Integer.parseInt(m.eval(c,false).toString())==Integer.parseInt(UBound.toString())){
			 writer.append(""+m.eval(c,false)+"(UBound)");
		}else
		 	writer.append(""+m.eval(c,false));
		writer.append(',');
		writer.append(""+m.eval(tg,false));
		writer.append('\n');		
		//	}
			 // seek to next model
		BoolExpr ba = ctx.mkEq(a,(IntExpr) m.eval(a,false));
		BoolExpr bb = ctx.mkEq(b,(IntExpr) m.eval(b,false));
		BoolExpr bc = ctx.mkEq(c,(IntExpr) m.eval(c,false));
		BoolExpr babc = ctx.mkEq(abc,(IntExpr) m.eval(abc,false));
		
		BoolExpr aa = ctx.mkAnd(ctx.mkNot(ctx.mkEq(a,LBound)),ctx.mkNot(ctx.mkEq(b,LBound)));
		BoolExpr bba = ctx.mkAnd(ctx.mkEq(b,LBound),ctx.mkEq(c,LBound));
		BoolExpr cc = ctx.mkAnd(ctx.mkEq(a,LBound),ctx.mkEq(c,LBound));
		BoolExpr bEQUI = ctx.mkEq(CheckEQUI,(BoolExpr) m.eval(CheckEQUI,false));
		BoolExpr bISO = ctx.mkEq(CheckISO,(BoolExpr) m.eval(CheckISO,false));
		BoolExpr bSCA = ctx.mkEq(CheckSCA,(BoolExpr) m.eval(CheckSCA,false));		    
		BoolExpr bNOT = ctx.mkEq(CheckNOT,(BoolExpr) m.eval(CheckNOT,false));
		    
		s.add(ctx.mkOr(ctx.mkAnd(ctx.mkOr(ctx.mkEq(ba,ctx.mkFalse()),ctx.mkEq(bb,ctx.mkFalse()),ctx.mkEq(bc,ctx.mkFalse())),bEQUI),
				ctx.mkAnd(ctx.mkOr(ctx.mkEq(ba,ctx.mkFalse()),ctx.mkEq(bb,ctx.mkFalse()),ctx.mkEq(bc,ctx.mkFalse())),bISO),
				ctx.mkAnd(ctx.mkOr(ctx.mkEq(ba,ctx.mkFalse()),ctx.mkEq(bb,ctx.mkFalse()),ctx.mkEq(bc,ctx.mkFalse())),bSCA),
				ctx.mkAnd(ctx.mkOr(ctx.mkEq(ba,ctx.mkFalse()),ctx.mkEq(bb,ctx.mkFalse()),ctx.mkEq(bc,ctx.mkFalse())),bNOT)));
		s.add(ctx.mkOr(ctx.mkAnd(ctx.mkLe(a,NLBound),ctx.mkLe(c,NLBound),ctx.mkLe(c,NLBound)),
				ctx.mkAnd(ctx.mkGe(a,NUBound),ctx.mkGe(c,NUBound),ctx.mkGe(c,NUBound)),
				ctx.mkAnd(ctx.mkAnd(ctx.mkGt(a,MidVal),ctx.mkGt(c,MidVal),ctx.mkGt(c,MidVal)),
				ctx.mkAnd(ctx.mkLe(a,MidVal),ctx.mkLe(c,MidVal),ctx.mkLe(c,MidVal)))));
		//,ctx.mkEq(bEQUI,ctx.mkFalse()),ctx.mkEq(bSCA,ctx.mkFalse()),ctx.mkEq(bISO,ctx.mkFalse())));
//		s.add(ctx.mkOr(ctx.mkEq(aa,ctx.mkFalse()), ctx.mkEq(bba,ctx.mkFalse()),ctx.mkEq(cc,ctx.mkFalse())));
//		s.add(ctx.mkOr(ctx.mkEq(ctx.mkEq(a,UBound),ctx.mkFalse()), ctx.mkEq(ctx.mkEq(b,UBound),ctx.mkFalse()),
//				ctx.mkEq(ctx.mkEq(c,UBound),ctx.mkFalse()),ctx.mkEq(ctx.mkEq(a,NUBound),ctx.mkFalse()),
//				ctx.mkEq(ctx.mkEq(b,NUBound),ctx.mkFalse()), ctx.mkEq(ctx.mkEq(c,NUBound),ctx.mkFalse()),
//				ctx.mkEq(ctx.mkEq(a,LBound),ctx.mkFalse()),ctx.mkEq(ctx.mkEq(b,LBound),ctx.mkFalse()),ctx.mkEq(ctx.mkEq(c,LBound),ctx.mkFalse())));
		// Random values
		//s.add(ctx.mkOr(ctx.mkAnd(ctx.mkEq(a, da[0]),ctx.mkEq(b, db[0]),ctx.mkEq(c, dc[0])),ctx.mkAnd(ctx.mkEq(a, da[1]),ctx.mkEq(b, db[1]),ctx.mkEq(c, dc[1])),ctx.mkAnd(ctx.mkEq(a, da[2]),ctx.mkEq(b, db[2]),ctx.mkEq(c, dc[2])),ctx.mkAnd(ctx.mkEq(a, da[3]),ctx.mkEq(b, db[3]),ctx.mkEq(c, dc[3])),ctx.mkAnd(ctx.mkEq(a, da[4]),ctx.mkEq(b, db[4]),ctx.mkEq(c, dc[4]))));
	//	s.add(ctx.mkOr(ctx.mkEq(a, LBound),ctx.mkEq(b, LBound),ctx.mkEq(c, LBound),ctx.mkEq(a, UBound),ctx.mkEq(b, UBound),ctx.mkEq(c, UBound),ctx.mkAnd(ctx.mkEq(a, da[0]),ctx.mkEq(b, db[0]),ctx.mkEq(c, dc[0])),ctx.mkAnd(ctx.mkEq(a, da[1]),ctx.mkEq(b, db[1]),ctx.mkEq(c, dc[1])),ctx.mkAnd(ctx.mkEq(a, da[2]),ctx.mkEq(b, db[2]),ctx.mkEq(c, dc[2])),ctx.mkAnd(ctx.mkEq(a, da[3]),ctx.mkEq(b, db[3]),ctx.mkEq(c, dc[3])),ctx.mkAnd(ctx.mkEq(a, da[4]),ctx.mkEq(b, db[4]),ctx.mkEq(c, dc[4]))));
		i++;
       }
//check Invalid partition
     si.add(CheckInvalid);
     int j=0;
     while(si.check() == Status.SATISFIABLE && j< 6){
		 p.add("random_seed", j);
		 si.setParameters(p);	
    	m = si.getModel(); // get value and print out
		writer.append(""+ m.eval(a,false));
		writer.append(',');
		writer.append(""+m.eval(b,false));
		writer.append(',');
	 	writer.append(""+m.eval(c,false));
		writer.append(',');
		writer.append("INVALID");
		writer.append('\n');		
		//	}
			 // seek to next model
		BoolExpr iba = ctx.mkEq(a,(IntExpr) m.eval(a,false));
		BoolExpr ibb = ctx.mkEq(b,(IntExpr) m.eval(b,false));
		BoolExpr ibc = ctx.mkEq(c,(IntExpr) m.eval(c,false));
		    
		si.add(ctx.mkOr(ctx.mkEq(iba,ctx.mkFalse()),ctx.mkEq(ibb,ctx.mkFalse()),ctx.mkEq(ibc,ctx.mkFalse()),CheckInvalid));

		j++;
       }
     
// Close file
	    long t_diff2 = ((new Date()).getTime() - before.getTime());// / 1000;
        System.out.println("SMT2 file test took " + t_diff2 + " ms");
	    writer.flush();
	    writer.close();

	    System.out.println("Success!");
	}

}
