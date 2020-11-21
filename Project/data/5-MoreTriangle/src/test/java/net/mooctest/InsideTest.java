package net.mooctest;

import static org.evosuite.runtime.EvoAssertions.verifyException;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import org.junit.Test;


public class InsideTest{

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
  public void test10()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle();
      // Undeclared exception!
      try { 
        moreTriangle0.pointInsideTriangle(0.0, 0.0);
        fail("Expecting exception: NullPointerException");
      
      } catch(NullPointerException e) {
  
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
}
