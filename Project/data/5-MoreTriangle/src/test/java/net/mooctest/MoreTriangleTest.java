package net.mooctest;

import static org.evosuite.runtime.EvoAssertions.verifyException;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import org.junit.Test;


public class MoreTriangleTest{

  @Test(timeout = 4000)
  public void test02()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle("", 0.0, 0.0, 0.0, 0.5, 0.0, 0.0);
      double double0 = moreTriangle0.getCentroidY();
      assertEquals(0.0, moreTriangle0.getCentroidX(), 0.01);
      assertEquals(0.16666666666666666, double0, 0.01);
  }

  @Test(timeout = 4000)
  public void test03()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle(0.0, 0.0, (-0.5), 0.0, 0.0, 0.0);
      double double0 = moreTriangle0.getCentroidX();
      assertEquals((-0.16666666666666666), double0, 0.01);
      assertEquals(0.0, moreTriangle0.getCentroidY(), 0.01);
  }

  @Test(timeout = 4000)
  public void test05()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle(0.0, 0.0, 0.0, 0.0, 0.0, 0.6372539602871093);
      double double0 = moreTriangle0.getCentroidY();
      assertEquals(0.21241798676236978, double0, 0.01);
      assertEquals(0.0, moreTriangle0.getCentroidX(), 0.01);
  }

  @Test(timeout = 4000)
  public void test06()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle("", 0.0, (-2.2527732910156253), 0.0, 0.0, 0.0, 0.0);
      double double0 = moreTriangle0.getCentroidY();
      assertEquals(0.0, moreTriangle0.getCentroidX(), 0.01);
      assertEquals((-0.7509244303385417), double0, 0.01);
  }

  @Test(timeout = 4000)
  public void test07()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle(0.0, 0.0, 0.0, 0.0, 0.52520673828125, 0.0);
      double double0 = moreTriangle0.getCentroidX();
      assertEquals(0.0, moreTriangle0.getCentroidY(), 0.01);
      assertEquals(0.17506891276041667, double0, 0.01);
  }

  @Test(timeout = 4000)
  public void test09()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle();
      // Undeclared exception!
      try { 
        moreTriangle0.toString();
        fail("Expecting exception: NullPointerException");
      
      } catch(NullPointerException e) {
         
      }
  }

  @Test(timeout = 4000)
  public void test12()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle();
      // Undeclared exception!
      try { 
        moreTriangle0.getCentroidY();
        fail("Expecting exception: NullPointerException");
      
      } catch(NullPointerException e) {
         verifyException("net.mooctest.MoreTriangle", e);
      }
  }

  @Test(timeout = 4000)
  public void test23()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle();
      // Undeclared exception!
      try { 
        moreTriangle0.getCentroidX();
        fail("Expecting exception: NullPointerException");
      
      } catch(NullPointerException e) {
      }
  }

  @Test(timeout = 4000)
  public void test25()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle("", 0.0, 0.0, 0.0, 0.0, 0.0, 0.0);
      double double0 = moreTriangle0.getCentroidY();
      assertEquals(0.0, double0, 0.01);
  }

  @Test(timeout = 4000)
  public void test26()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle(0.0, 0.0, 0.0, 0.0, 0.0, 0.0);
      double double0 = moreTriangle0.getCentroidX();
      assertEquals(0.0, double0, 0.01);
  }


  @Test(timeout = 4000)
  public void test28()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle("", 0.0, 0.0, 0.0, 0.0, 0.0, 0.0);
      String string0 = moreTriangle0.toString();
      assertEquals("Triangle: \"\"\n================================= \nEdge(\"e1\") connects nodes (n3, n1)\nEdge(\"e2\") connects nodes (n1, n2)\nEdge(\"e3\") connects nodes (n2, n3)\nNode(\"n3\") is at (0.0,0.0)\nNode(\"n1\") is at (0.0,0.0)\nNode(\"n2\") is at (0.0,0.0)\n================================= \n", string0);
  }
  
  
}
