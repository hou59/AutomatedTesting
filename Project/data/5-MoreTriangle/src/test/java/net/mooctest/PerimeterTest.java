package net.mooctest;

import static org.evosuite.runtime.EvoAssertions.verifyException;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import org.junit.Test;


public class PerimeterTest{

  @Test(timeout = 4000)
  public void test04()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle(0.0, 0.0, 0.0, 0.0, 0.0, (-0.5));
      double double0 = moreTriangle0.perimeter();
      assertEquals(1.0, double0, 0.01);
      assertEquals((-0.16666666666666666), moreTriangle0.getCentroidY(), 0.01);
  }

  @Test(timeout = 4000)
  public void test11()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle();
      // Undeclared exception!
      try { 
        moreTriangle0.perimeter();
        fail("Expecting exception: NullPointerException");
      
      } catch(NullPointerException e) {
         verifyException("net.mooctest.MoreTriangle", e);
      }
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
}
