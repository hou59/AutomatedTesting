package net.mooctest;

import static org.evosuite.runtime.EvoAssertions.verifyException;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import org.junit.Test;


public class MoreTriangleTest{

  @Test(timeout = 4000)
  public void test00() {
      MoreTriangle moreTriangle = new MoreTriangle(0, 0, 0, 0, 0, 0);
  }
  
  @Test(timeout = 4000)
  public void test000()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle(1563.85, 1564.85, 1563.85, 1563.85, (-0.5), (-0.5));
      Edge edge0 = moreTriangle0.edge3;
      moreTriangle0.edge1 = edge0;
      boolean boolean0 = moreTriangle0.pointInsideTriangle(1563.85, 1563.85);
      assertEquals(1042.7333333333333, moreTriangle0.getCentroidY(), 0.01);
      assertTrue(boolean0);
      assertEquals(1042.3999999999999, moreTriangle0.getCentroidX(), 0.01);
  }

  @Test(timeout = 4000)
  public void test01()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle("", 0.0, 0.7481814741210937, 0.0, 0.7481814741210937, 0.0, 0.0);
      boolean boolean0 = moreTriangle0.pointInsideTriangle(0.0, 0.0);
      assertEquals(0.49878764941406245, moreTriangle0.getCentroidY(), 0.01);
      assertEquals(0.0, moreTriangle0.getCentroidX(), 0.01);
      assertFalse(boolean0);
  }

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
  public void test04()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle(0.0, 0.0, 0.0, 0.0, 0.0, (-0.5));
      double double0 = moreTriangle0.perimeter();
      assertEquals(1.0, double0, 0.01);
      assertEquals((-0.16666666666666666), moreTriangle0.getCentroidY(), 0.01);
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
  public void test08()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle(0.0, 1105.4743164062502, 0.0, 0.0, 0.0, (-0.5));
      Edge edge0 = moreTriangle0.edge3;
      moreTriangle0.edge1 = edge0;
      double double0 = moreTriangle0.area();
      assertEquals(276.4935720376552, double0, 0.01);
  }

  @Test(timeout = 4000)
  public void test09()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle();
      // Undeclared exception!
      try { 
        moreTriangle0.toString();
        fail("Expecting exception: NullPointerException");
      
      } catch(NullPointerException e) {
         //
         // no message in exception (getMessage() returned null)
         //
         
      }
  }

  @Test(timeout = 4000)
  public void test10()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle();
      // Undeclared exception!
      try { 
        moreTriangle0.pointInsideTriangle(0.0, 0.0);
        fail("Expecting exception: NullPointerException");
      
      } catch(NullPointerException e) {
         //
         // no message in exception (getMessage() returned null)
         //
         
      }
  }

  @Test(timeout = 4000)
  public void test11()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle();
      // Undeclared exception!
      try { 
        moreTriangle0.perimeter();
        fail("Expecting exception: NullPointerException");
      
      } catch(NullPointerException e) {
         //
         // no message in exception (getMessage() returned null)
         //
         verifyException("net.mooctest.MoreTriangle", e);
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
         //
         // no message in exception (getMessage() returned null)
         //
         verifyException("net.mooctest.MoreTriangle", e);
      }
  }

  @Test(timeout = 4000)
  public void test13()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle(0.0, 0.0, 0.0, 0.0, 0.0, 0.0);
      Edge edge0 = new Edge();
      moreTriangle0.edge2 = edge0;
      // Undeclared exception!
      try { 
        moreTriangle0.area();
        fail("Expecting exception: NullPointerException");
      
      } catch(NullPointerException e) {
         //
         // no message in exception (getMessage() returned null)
         //
         
      }
  }

  @Test(timeout = 4000)
  public void test14()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle((-134.572265625), (-0.96484375), (-989.0), (-134.88893505360062), (-134.88893505360062), 1757.6991876149027);
      boolean boolean0 = moreTriangle0.pointInsideTriangle((-134.88893505360062), (-0.5258357307294541));
      assertEquals((-419.48706689286684), moreTriangle0.getCentroidX(), 0.01);
      assertEquals(540.615136270434, moreTriangle0.getCentroidY(), 0.01);
      assertTrue(boolean0);
  }

  @Test(timeout = 4000)
  public void test15()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle("", 0.5, (-2566.6796999999997), 0.5, 0.5, 0.5, 0.5);
      boolean boolean0 = moreTriangle0.pointInsideTriangle((-2566.6796999999997), 0.0);
      assertEquals((-855.2265666666666), moreTriangle0.getCentroidY(), 0.01);
      assertFalse(boolean0);
      assertEquals(0.5, moreTriangle0.getCentroidX(), 0.01);
  }

  @Test(timeout = 4000)
  public void test16()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle(1563.3218261718748, 1563.3218261718748, 0.0, 0.0, 0.0, 0.0);
      boolean boolean0 = moreTriangle0.pointInsideTriangle(0.0, 0.7631103515625);
      assertEquals(521.107275390625, moreTriangle0.getCentroidY(), 0.01);
      assertEquals(521.107275390625, moreTriangle0.getCentroidX(), 0.01);
      assertFalse(boolean0);
  }

  @Test(timeout = 4000)
  public void test17()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle(0.0, 0.0, 0.0, (-0.8410086248066406), (-0.8410086248066406), 0.0);
      boolean boolean0 = moreTriangle0.pointInsideTriangle(0.0, 0.0);
      assertEquals((-0.2803362082688802), moreTriangle0.getCentroidX(), 0.01);
      assertTrue(boolean0);
  }

  @Test(timeout = 4000)
  public void test18()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle(0.0, 0.0, 1563.3218261718748, 1563.3218261718748, 0.0, 0.0);
      boolean boolean0 = moreTriangle0.pointInsideTriangle(0.0, 0.7631103515625);
      assertFalse(boolean0);
      assertEquals(521.107275390625, moreTriangle0.getCentroidX(), 0.01);
      assertEquals(521.107275390625, moreTriangle0.getCentroidY(), 0.01);
  }

  @Test(timeout = 4000)
  public void test19()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle(0.0, 0.0, 0.0, 748.5376098632812, 0.0, 0.0);
      boolean boolean0 = moreTriangle0.pointInsideTriangle(0.896142578125, 0.730054421484375);
      assertEquals(249.51253662109374, moreTriangle0.getCentroidY(), 0.01);
      assertFalse(boolean0);
      assertEquals(0.0, moreTriangle0.getCentroidX(), 0.01);
  }

  @Test(timeout = 4000)
  public void test20()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle(0.0, 0.0, 0.0, 748.5376098632812, 0.0, 0.0);
      boolean boolean0 = moreTriangle0.pointInsideTriangle(0.0, 0.730054421484375);
      assertFalse(boolean0);
      assertEquals(0.0, moreTriangle0.getCentroidX(), 0.01);
      assertEquals(249.51253662109374, moreTriangle0.getCentroidY(), 0.01);
  }

  @Test(timeout = 4000)
  public void test21()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle(0.0, 748.5376098632812, 0.0, 0.0, 0.0, 0.0);
      Edge edge0 = moreTriangle0.edge3;
      moreTriangle0.edge1 = edge0;
      boolean boolean0 = moreTriangle0.pointInsideTriangle(0.896142578125, 0.730054421484375);
      assertEquals(249.51253662109374, moreTriangle0.getCentroidY(), 0.01);
      assertFalse(boolean0);
      assertEquals(0.0, moreTriangle0.getCentroidX(), 0.01);
  }

  @Test(timeout = 4000)
  public void test22()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle(0.0, 0.0, 0.0, 0.0, 0.0, 0.0);
      boolean boolean0 = moreTriangle0.pointInsideTriangle(0.0, 0.0);
      assertFalse(boolean0);
  }

  @Test(timeout = 4000)
  public void test23()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle();
      // Undeclared exception!
      try { 
        moreTriangle0.getCentroidX();
        fail("Expecting exception: NullPointerException");
      
      } catch(NullPointerException e) {
         //
         // no message in exception (getMessage() returned null)
         //
         
      }
  }

  @Test(timeout = 4000)
  public void test24()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle(0.0, 0.0, 0.0, 0.0, 0.0, 0.0);
      double double0 = moreTriangle0.area();
      assertEquals(0.0, double0, 0.01);
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
  public void test27()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle(0.0, 0.0, 0.0, 0.0, 0.0, 0.0);
      double double0 = moreTriangle0.perimeter();
      assertEquals(0.0, double0, 0.01);
      assertEquals("Node(\"n3\") is at (0.0,0.0)",moreTriangle0.node1.toString());
      assertEquals("Node(\"n1\") is at (0.0,0.0)",moreTriangle0.node2.toString());
      assertEquals("Node(\"n2\") is at (0.0,0.0)",moreTriangle0.node3.toString());
  }

  @Test(timeout = 4000)
  public void test28()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle("", 0.0, 0.0, 0.0, 0.0, 0.0, 0.0);
      String string0 = moreTriangle0.toString();
      assertEquals("Triangle: \"\"\n================================= \nEdge(\"e1\") connects nodes (n3, n1)\nEdge(\"e2\") connects nodes (n1, n2)\nEdge(\"e3\") connects nodes (n2, n3)\nNode(\"n3\") is at (0.0,0.0)\nNode(\"n1\") is at (0.0,0.0)\nNode(\"n2\") is at (0.0,0.0)\n================================= \n", string0);
  }
  
  @Test(timeout = 4000)
  public void test29()  throws Throwable  {
	  Vector v1 = new Vector(1,0);
      Vector v2 = new Vector(2.0, 3.0);
      assertEquals("Vector(3.0, 3.0)", v1.add(v2).toString());
      assertEquals("Vector(-1.0, -3.0)", v1.sub(v2).toString());
  }
  
  @Test(timeout = 4000)
  public void test30()  throws Throwable  {
	  MoreTriangle m = new MoreTriangle("", 0.0, 0.0, 0.0, 0.0, 0.0, 0.0);
  }
}
