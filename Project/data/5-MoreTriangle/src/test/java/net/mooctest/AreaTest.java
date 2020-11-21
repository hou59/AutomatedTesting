package net.mooctest;

import static org.evosuite.runtime.EvoAssertions.verifyException;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import org.junit.Test;


public class AreaTest{

  @Test(timeout = 4000)
  public void test08()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle(0.0, 1105.4743164062502, 0.0, 0.0, 0.0, (-0.5));
      Edge edge0 = moreTriangle0.edge3;
      moreTriangle0.edge1 = edge0;
      double double0 = moreTriangle0.area();
      assertEquals(276.4935720376552, double0, 0.01);
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

      }
  }

  @Test(timeout = 4000)
  public void test24()  throws Throwable  {
      MoreTriangle moreTriangle0 = new MoreTriangle(0.0, 0.0, 0.0, 0.0, 0.0, 0.0);
      double double0 = moreTriangle0.area();
      assertEquals(0.0, double0, 0.01);
  }
}
