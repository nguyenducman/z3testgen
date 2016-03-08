package net.z3testgen;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;
import com.microsoft.z3.*;

public class ReadSMTLibFile {
	/*
	 * 
		;CanMarry - pre: 0<=age<=150; return value
		(declare-const age Int)
		(declare-const isMale Bool)
		(declare-fun f (Int Bool) Bool)
		(assert (and (<= 0 age) (<= age 150)))
		(assert (or isMale (not isMale)))
		(assert (f age isMale))
		
	 * 
	 */
	public static void main(String[] args) throws Z3Exception, IOException  {
		
		 Date before = new Date();
	
	        System.out.println("SMT2 File test ");
	        System.gc();

	        {
	            Context ctx = new Context();
	            BoolExpr expr = ctx.parseSMTLIB2File("input/canMarry2.smt2",null,null,null,null);
	   		 	Tactic smtTactic = ctx.mkTactic("smt");
	   	
	   		 	Params p = ctx.mkParams();
	   		 	//p.add("arith.random_initial_value", true);
					 
	  		 	Tactic using = ctx.usingParams(smtTactic, p); //then(simplifyTactic, smtTactic, new Tactic[] {});
	   		 	Solver s = ctx.mkSolver(using);
	   		 	Solver si = ctx.mkSolver(using);
	            Model m = null;
	   
	//    		IntExpr age = ctx.mkIntConst("age");
	            //s.setParameters(p);
	    		s.add(expr);si.add(expr);
	    		
	            long t_diff = ((new Date()).getTime() - before.getTime());// / 1000;

	            System.out.println("SMT2 file read time: " + t_diff + " msec");
	            // Iterate over the formula.
	            int i=0;
	            IntExpr age;
	            BoolExpr isMale;
	          //write solution to csv file  
	       	 FileWriter writer = new FileWriter("output/CanMarry.csv");
	            System.out.println("model for: CanMarry");
	       	 writer.append("age");
	       	 writer.append(',');
	       	 writer.append("Gender");
	       	 writer.append(',');
	       	 writer.append("CanMarry");
	       	 writer.append('\n');

	         while (s.check()== Status.SATISFIABLE ){
	            	i++;
//	            	
	       		 	p.add("random_seed", i);
	       		 	s.setParameters(p);	
	            	m=s.getModel();          	
	            	age =  ctx.mkIntConst(m.getConstDecls()[1].getName());  
	            	isMale =ctx.mkBoolConst(m.getConstDecls()[2].getName());

//	    	        System.out.println(m.getConstDecls()[0].getName());	  
	    	        //get value of variable
/*
 * Can configure:
 * age >=149; age = 75; age >=16 and <18; age 18-19; age <=1
 * or combine isMale is true with age >=16 and <18; age 18-19; age <=1
 * or combine isMale is false with age >=16 and <18; age 18-19; age <=1
 */
	    	        s.add(ctx.mkOr(ctx.mkEq(ctx.mkEq(age, m.eval(m.getConstInterp(m.getConstDecls()[1]), false)), ctx.mkFalse())));
	    	        s.add(ctx.mkOr(ctx.mkGe(age, ctx.mkInt(149)),ctx.mkEq(age, ctx.mkInt(75)),ctx.mkLe(age, ctx.mkInt(1)),
	    	        		//ctx.mkAnd(ctx.mkEq(isMale,  ctx.mkTrue()),ctx.mkAnd(ctx.mkLe(age, ctx.mkInt(15)),ctx.mkGe(age, ctx.mkInt(13)))),
	    	        		ctx.mkAnd(ctx.mkEq(isMale,  ctx.mkFalse()),ctx.mkAnd(ctx.mkLe(age, ctx.mkInt(15)),ctx.mkGe(age, ctx.mkInt(13)))),
	    	        		ctx.mkAnd(ctx.mkGe(age, ctx.mkInt(16)),ctx.mkLe(age, ctx.mkInt(19)),ctx.mkEq(isMale,  ctx.mkFalse())),
	    	        		ctx.mkAnd(ctx.mkGe(age, ctx.mkInt(16)),ctx.mkLe(age, ctx.mkInt(19)),ctx.mkEq(isMale,  ctx.mkTrue()))
	    	        		));

	    	        writer.append(""+m.eval(m.getConstInterp(m.getConstDecls()[1]), false));
	    	        writer.append(',');
	    	        writer.append(""+m.eval(m.getConstInterp(m.getConstDecls()[2]), false));
	    	        writer.append(',');
	    	        writer.append(""+m.eval(m.getConstInterp(m.getConstDecls()[0]), false));
	    	        writer.append('\n');
	    	        
	            } 	
//========== invalid value ===============
	         i=0;
	         si.add(ctx.mkOr(ctx.mkLt(ctx.mkIntConst(m.getConstDecls()[1].getName()),ctx.mkInt(0)),ctx.mkGt(ctx.mkIntConst(m.getConstDecls()[1].getName()),ctx.mkInt(150))));
	         while (si.check()== Status.SATISFIABLE && i <5){
	            	i++;
//	            	
	       		 	p.add("random_seed", i);
	       		 	si.setParameters(p);	
	            	m=si.getModel();          	
	            	age =  ctx.mkIntConst(m.getConstDecls()[1].getName());  
	            	isMale =ctx.mkBoolConst(m.getConstDecls()[2].getName());
	    	        si.add(ctx.mkOr(ctx.mkEq(ctx.mkEq(age, m.eval(m.getConstInterp(m.getConstDecls()[1]), false)), ctx.mkFalse())));
	    	        writer.append(""+m.eval(m.getConstInterp(m.getConstDecls()[1]), false));
	    	        writer.append(',');
	    	        writer.append(""+m.eval(m.getConstInterp(m.getConstDecls()[2]), false));
	    	        writer.append(',');
	    	        writer.append(""+m.eval(m.getConstInterp(m.getConstDecls()[0]), false));
	    	        writer.append('\n');
	    	        
	            } 		         
	 	    writer.flush();
		    writer.close();

		    System.out.println("Success!");
	        }

	        long t_diff = ((new Date()).getTime() - before.getTime());// / 1000;
	        System.out.println("SMT2 file test took " + t_diff + " msec");
	       

	}

}
