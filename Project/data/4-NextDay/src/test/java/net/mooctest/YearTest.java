package net.mooctest;

import static org.junit.Assert.*;
import org.junit.Test;

public class YearTest {
	Year obj = new Year(1);
	
	@Test
	public void testGetCurrent() {
		obj.currentPos = 1992;
		int actual = obj.getCurrentPos();
		assertEquals(1992,actual);
	}
	
	@Test
	public void testSetCurrent() {
		obj.setCurrentPos(1992);
		assertEquals(1992, obj.currentPos);
	}
	
	@Test
	public void testEquals1() {
		Year obj1 = new Year(1);
		
		assertTrue(obj.equals(obj1));
	}
	
	@Test
	public void testEquals2() {
		Year obj1 = new Year(1992);
		
		assertFalse(obj.equals(obj1));
	}
	
	@Test
	public void testEquals3() {
			assertFalse(obj.equals("hello"));
	}
	
	@Test
	public void testEquals4() {
			assertFalse(obj.equals(null));
	}
	
	@Test
	public void testGetYear() {
		obj.currentPos = 1992;
		int actual = obj.getYear();
		assertEquals(1992,actual);
	}
	
	@Test
	public void testSetYear() {
		obj.setYear(-1);		
		assertEquals(-1, obj.currentPos);
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void testSetYearException() {
		obj.setYear(0);
	}
	
	@Test
	public void testIncrement1() {
		assertTrue(obj.increment());		
	}
	
	@Test
	public void testIncrement2() {
		obj.increment();
		assertEquals(2,obj.currentPos);
	}
	
	@Test
	public void testIncrement3() {
		obj.currentPos = -1;
		assertTrue(obj.increment());  		
	}
	
	@Test
	public void testIncrement4() {
		obj.currentPos = -1;
		obj.increment();
		assertEquals(1,obj.currentPos);
	}
	
	@Test
	public void testIncrement5() {
		obj.currentPos = -2;
		assertTrue(obj.increment());  		
	}
	
	@Test
	public void testIncrement6() {
		obj.currentPos = -2;
		obj.increment();
		assertEquals(-1,obj.currentPos);
	}
	@Test
	public void testIsValid1() {
		assertTrue(obj.isValid());
	}
	
	@Test
	public void testIsValid2() {
		obj.currentPos = -1;
		assertTrue(obj.isValid());
	}
	
	@Test
	public void testIsValid3() {
		obj.currentPos = 0;
		assertFalse(obj.isValid());
	}	
}
