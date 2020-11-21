package net.mooctest;

import static org.junit.Assert.*;

import org.junit.Test;

public class CalendarUnitTest {
	@Test(timeout = 4000)
	  public void test0()  throws Throwable  {
	      Year year0 = new Year((-1));
	      assertEquals((-1), year0.getYear());
	      
	      year0.setCurrentPos(0);
	      int int0 = year0.getCurrentPos();
	      assertEquals(0, int0);
	  }

	  @Test(timeout = 4000)
	  public void test1()  throws Throwable  {
	      Year year0 = new Year(1);
	      int int0 = year0.getCurrentPos();
	      assertEquals(1, int0);
	  }

	  @Test(timeout = 4000)
	  public void test2()  throws Throwable  {
	      Year year0 = new Year((-1));
	      int int0 = year0.getCurrentPos();
	      assertEquals((-1), int0);
	  }

}
