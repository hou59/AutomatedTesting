package net.mooctest;

import static org.junit.Assert.*;

import java.lang.reflect.Field;

import org.junit.Test;

public class DayTest {
	Year y = new Year(1991);
	Month m = new Month(6,y);
	Day d = new Day(16,m);//1991-6-16
	
	@Test
	public void testGetCurrentPos() {
		d.currentPos = 2;
		assertEquals(2, d.getCurrentPos());
	}
	
	@Test
	public void testSetCurrentPos() {
		d.setCurrentPos(10);
		assertEquals(10, d.currentPos);
	}
	
	@Test
	public void testGetDay() {
		d.currentPos = 21;
		assertEquals(21, d.getDay());
	}

	@Test
	public void testEquals1() {
		assertFalse(d.equals(null));
	}
	
	@Test
	public void testEquals2() {
		assertFalse(d.equals(m));
	}
	
	@Test
	public void testEquals3() {
		Day d1 = new Day(15, m);
		
		assertFalse(d.equals(d1));
	}
	
	@Test
	public void testEquals4() {
		Month m1 = new Month(7,y);
		Day d1 = new Day(16, m1);
		
		assertFalse(d.equals(d1));
	}
	
	@Test
	public void testEquals5() {
		Day d1 = new Day(16, m);
		
		assertTrue(d.equals(d1));
	}
	
	@Test
	public void testIncrement1() {
		d.currentPos = 28; //1991-6-28
		d.increment();
		assertEquals(29,d.currentPos);
	}
	
	@Test
	public void testIncrement2() {
		d.currentPos = 28; //1991-6-28
		assertTrue(d.increment());
	}
	
	@Test
	public void testIncrement3() {
		d.currentPos = 29; //1991-6-29
		d.increment();
		assertEquals(30,d.currentPos);
	}
	
	@Test
	public void testIncrement4() {
		d.currentPos = 29; //1991-6-29
		assertTrue(d.increment());
	}
	
	@Test
	public void testIncrement5() {
		d.currentPos = 30; //1991-6-30
		d.increment();
		assertEquals(31,d.currentPos);
	}
	
	@Test
	public void testIncrement6() {
		d.currentPos = 30; //1991-6-30
		assertFalse(d.increment());
	}
	
	@Test
	public void testIsValid() throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
		Field f = Day.class.getDeclaredField("m");
		f.setAccessible(true);
		
		f.set(d, null);
		
		assertFalse(d.isValid());		
	}
	
	@Test
	public void testSetDay1() {
		Month m1 = new Month(10, y);
		d.setDay(20, m1);
		
		assertEquals(20, d.currentPos);
	}
	
	@Test
	public void testSetDay2() throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
		Month m1 = new Month(10, y);
		d.setDay(20, m1);
		
		Field f = Day.class.getDeclaredField("m");
		f.setAccessible(true);
		
		assertEquals(m1, f.get(d) );
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void testSetDay3() {
		d.setDay(32, m);
	}	
}
