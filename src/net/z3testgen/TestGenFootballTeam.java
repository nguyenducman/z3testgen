package net.z3testgen;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;
import com.microsoft.z3.*;

public class TestGenFootballTeam {
	
	public static void main(String[] args) throws Z3Exception, IOException  {
		
		 Date before = new Date();
	
	        System.out.println("Football Team... ");
	        System.gc();

	        {
	            Context ctx = new Context();
	            BoolExpr expr = ctx.parseSMTLIB2File("input/Football2.smt2",null,null,null,null);
	            BoolExpr expr2 = ctx.parseSMTLIB2File("input/Football.smt2",null,null,null,null);
	   		 	Tactic smtTactic = ctx.mkTactic("smt");
	   	
	   		 	Params p = ctx.mkParams();
	   		 	//p.add("arith.random_initial_value", true);
					 
	  		 	Tactic using = ctx.usingParams(smtTactic, p); //then(simplifyTactic, smtTactic, new Tactic[] {});
	   		 	Solver s = ctx.mkSolver(using);
	   		 	Solver si = ctx.mkSolver(using);
	            Model m = null;
	   
	//    		Declare invariant
	            IntExpr win;
	            IntExpr draw;
	            IntExpr lose;
	            IntExpr point;
	            //s.setParameters(p);
	    			    		
	            long t_diff = ((new Date()).getTime() - before.getTime());// / 1000;

	            System.out.println("SMT2 file read time: " + t_diff + " msec");
	            // Iterate over the formula.
	            
	          //write solution to csv file  
	       	 FileWriter writer = new FileWriter("data/Football.csv");
	            System.out.println("model for: Football team");
	       	 writer.append("win");
	       	 writer.append(',');
	       	 writer.append("draw");
	       	 writer.append(',');
	       	 writer.append("lose");
	       	 writer.append(',');
	       	 writer.append("point");
	       	 writer.append('\n');
	       	 
	       	s.add(expr);
	       	int i=0;
	         while (s.check()== Status.SATISFIABLE  && i<30){
	            	i++;
//	            	
	       		 	p.add("random_seed", i);
	       		 	s.setParameters(p);	
	            	m=s.getModel();          	
	            	win =  ctx.mkIntConst(m.getConstDecls()[0].getName());  
	            	draw =   ctx.mkIntConst(m.getConstDecls()[2].getName());
	            	lose =  ctx.mkIntConst(m.getConstDecls()[3].getName());
	            	point =  ctx.mkIntConst(m.getConstDecls()[1].getName());
	    	        //get value of variable

	    	        s.add(ctx.mkOr(ctx.mkEq(ctx.mkEq(win, m.eval(m.getConstInterp(m.getConstDecls()[0]), false)), ctx.mkFalse()),
	    	        		ctx.mkEq(ctx.mkEq(draw, m.eval(m.getConstInterp(m.getConstDecls()[2]), false)), ctx.mkFalse()),
	    	        		ctx.mkEq(ctx.mkEq(lose, m.eval(m.getConstInterp(m.getConstDecls()[3]), false)), ctx.mkFalse()),
	    	        		ctx.mkEq(ctx.mkEq(point, m.eval(m.getConstInterp(m.getConstDecls()[1]), false)), ctx.mkFalse())));

	    	        writer.append(""+m.eval(m.getConstInterp(m.getConstDecls()[0]), false));
	    	        writer.append(',');
	    	        writer.append(""+m.eval(m.getConstInterp(m.getConstDecls()[2]), false));
	    	        writer.append(',');
	    	        writer.append(""+m.eval(m.getConstInterp(m.getConstDecls()[3]), false));
	    	        writer.append(',');
	    	        writer.append(""+m.eval(m.getConstInterp(m.getConstDecls()[1]), false));
	    	        writer.append('\n');
	    	        
	            } 	
//========== invalid value ===============
	         i=0;
	         si.add(expr2);
         while (si.check()== Status.SATISFIABLE && i <5){
	            	i++;
//	            	
	       		 	p.add("random_seed", i);
	       		 	si.setParameters(p);	
	            	m=si.getModel();          	
	            	win =  ctx.mkIntConst(m.getConstDecls()[0].getName());  
	            	draw =   ctx.mkIntConst(m.getConstDecls()[2].getName());
	            	lose =  ctx.mkIntConst(m.getConstDecls()[3].getName());
	            	point =  ctx.mkIntConst(m.getConstDecls()[1].getName());
	    	        //get value of variable

	    	        si.add(ctx.mkOr(ctx.mkEq(ctx.mkEq(win, m.eval(m.getConstInterp(m.getConstDecls()[0]), false)), ctx.mkFalse()),
	    	        		ctx.mkEq(ctx.mkEq(draw, m.eval(m.getConstInterp(m.getConstDecls()[2]), false)), ctx.mkFalse()),
	    	        		ctx.mkEq(ctx.mkEq(lose, m.eval(m.getConstInterp(m.getConstDecls()[3]), false)), ctx.mkFalse()),
	    	        		ctx.mkEq(ctx.mkEq(point, m.eval(m.getConstInterp(m.getConstDecls()[1]), false)), ctx.mkFalse())));

	    	        writer.append(""+m.eval(m.getConstInterp(m.getConstDecls()[0]), false));
	    	        writer.append(',');
	    	        writer.append(""+m.eval(m.getConstInterp(m.getConstDecls()[2]), false));
	    	        writer.append(',');
	    	        writer.append(""+m.eval(m.getConstInterp(m.getConstDecls()[3]), false));
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
