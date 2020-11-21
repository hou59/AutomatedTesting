package net.mooctest;

import static org.evosuite.runtime.EvoAssertions.verifyException;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import org.junit.Test;


public class VectorTest{
  
  @Test(timeout = 4000)
  public void test29()  throws Throwable  {
	  Vector v1 = new Vector(1,0);
      Vector v2 = new Vector(2.0, 3.0);
      assertEquals("Vector(3.0, 3.0)", v1.add(v2).toString());
      assertEquals("Vector(-1.0, -3.0)", v1.sub(v2).toString());
  }
  
}
