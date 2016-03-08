package net.z3testgen;

import java.util.Scanner;

enum Triangle
{ 
ISOSCELES,
EQUILATERAL,
SCALENE,
INVALID;
}
public class TriangleType {

	static Triangle getType(int a, int b, int c)
    {
        if(a<=0||b<=0||c<=0){
        	System.out.println("Length of sides cannot be equal to or less than zero");
        	return Triangle.INVALID;
        }
//        int ab = a+b;
//        int ac = a+c;
//        int bc = b+c;
        if (a>=b+c || b >=a+c || c>=a+b){
        	System.out.println("Sum of 2 sides can not equal to the other side");
        	System.out.println (a+b);
        	return Triangle.INVALID;        	
        }
        if(a==b&&b==c)
            return Triangle.EQUILATERAL;
        else if((a==b)||(b==c)||(c==a))
            return Triangle.ISOSCELES;
        else return Triangle.SCALENE;
    }
    public static void main(String[] args)
    {
    	int side_a,side_b,side_c;
    	Scanner sc = new Scanner(System.in);
    
    	int cont =1;
    	while (cont!=0){
    		System.out.println ("\nEnter side a length: ");
    		side_a= sc.nextInt();
    		System.out.println ("\nEnter side b length: ");
    		side_b= sc.nextInt();
    		System.out.println ("\nEnter side c length: ");
    		side_c= sc.nextInt();
  		
    		System.out.println(TriangleType.getType(side_a,side_b,side_c));
    		
            // Ask user if they want to continue.
            System.out.println ("\nDo you want to examine more triangles?");
            System.out.println ("(type 1 for yes or 0 for no)");
            cont = sc.nextInt();
    	}
    	sc.close();
    }
}

