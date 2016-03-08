package net.z3testgen;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;
import com.microsoft.z3.*;

public class TestGenPairwise {
	
	public static void main(String[] args) throws Z3Exception, IOException  {
		
		 Date before = new Date();
		 	

	
	        System.out.println("Pairwise testing... ");
	        System.gc();

	        {
	            Context ctx = new Context();
	            BoolExpr expr = ctx.parseSMTLIB2File("input/Pairwise.smt2",null,null,null,null);
	//            BoolExpr expr2 = ctx.parseSMTLIB2File("input/Football.smt2",null,null,null,null);
	   		 	Tactic smtTactic = ctx.mkTactic("smt");
	   	
	   		 	Params p = ctx.mkParams();
	   		 	//p.add("arith.random_initial_value", true);
					 
	  		 	Tactic using = ctx.usingParams(smtTactic, p); //then(simplifyTactic, smtTactic, new Tactic[] {});
	   		 	Solver s = ctx.mkSolver(using);
	   		 	Solver si = ctx.mkSolver(using);
	            Model m = null;
	
	//    		Declare invariant
	            Expr v1;
	            Expr v2;
	            Expr v3;
	      
	            //s.setParameters(p);
	       	 	Symbol name1 = ctx.mkSymbol("Type1");
	       	 	EnumSort Type11 = ctx.mkEnumSort(name1, ctx.mkSymbol("Val1A"),
	    	         ctx.mkSymbol("Val1B"), ctx.mkSymbol("Val1C"));	  
	       	 	Symbol name2 = ctx.mkSymbol("Type2");
	       	 	EnumSort Type21 = ctx.mkEnumSort(name2, ctx.mkSymbol("Val2A"),
	    	         ctx.mkSymbol("Val2B"), ctx.mkSymbol("Val2C"),ctx.mkSymbol("Val2D"));	
	       	 	Symbol name3 = ctx.mkSymbol("Type3");
	       	 	EnumSort Type31 = ctx.mkEnumSort(name3, ctx.mkSymbol("Val3A"),
	    	         ctx.mkSymbol("Val3B"), ctx.mkSymbol("Val3C"));	
	       	 	
	            long t_diff = ((new Date()).getTime() - before.getTime());// / 1000;

	            System.out.println("SMT2 file read time: " + t_diff + " msec");
	            // Iterate over the formula.
	            
	          //write solution to csv file  
	       	 FileWriter writer = new FileWriter("data/Pairwise.csv");
	            System.out.println("model for: Pairwise");
	       	 writer.append("v1");
	       	 writer.append(',');
	       	 writer.append("v2");
	       	 writer.append(',');
	       	 writer.append("v3");
	       	 writer.append('\n');
	       	 Sort a = null;
	       	s.add(expr);
	       	int i=0;
	         while (s.check()== Status.SATISFIABLE ){
	            	i++;
//	            	
	 //      		 	p.add("random_seed", i);
	//       		 	s.setParameters(p);	
	            	m=s.getModel();          	

	            	v2 =   ctx.mkConst(m.getConstDecls()[0].getName(), Type21);
	            	v3 =   ctx.mkConst(m.getConstDecls()[1].getName(), Type31);
	            	v1 =   ctx.mkConst(m.getConstDecls()[2].getName(), Type11);
	   	        //get value of variable

	    	        s.add(ctx.mkOr(ctx.mkEq(ctx.mkEq(v1, m.eval(m.getConstInterp(m.getConstDecls()[2]), false)), ctx.mkFalse()),
	    	        		ctx.mkEq(ctx.mkEq(v2, m.eval(m.getConstInterp(m.getConstDecls()[0]), false)), ctx.mkFalse()),
	    	        		ctx.mkEq(ctx.mkEq(v3, m.eval(m.getConstInterp(m.getConstDecls()[1]), false)), ctx.mkFalse())));

	    	        writer.append(""+m.eval(m.getConstInterp(m.getConstDecls()[2]), false));
	    	        writer.append(',');
	    	        writer.append(""+m.eval(m.getConstInterp(m.getConstDecls()[0]), false));
	    	        writer.append(',');
	    	        writer.append(""+m.eval(m.getConstInterp(m.getConstDecls()[1]), false));
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
