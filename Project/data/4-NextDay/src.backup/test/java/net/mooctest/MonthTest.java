package net.mooctest;

import static org.junit.Assert.*;

import java.lang.reflect.Field;

import org.junit.Test;

public class MonthTest {
	Year y1 = new Year(1991);
	Year y2 = new Year(2000);
	
	Month m1 = new Month(2, y1); //1991-2
	Month m2 = new Month(2,y2); //2000-2
	
	@Test
	public void testGetCurrentPos() {
		m1.currentPos = 2;
			
		assertEquals(2, m1.getCurrentPos());
	}
	
	@Test
	public void testSetCurrentPos() {
		m1.setCurrentPos(1);
		
		assertEquals(1,m1.currentPos);
	}
	
	@Test
	public void testGetMonth() {
		m1.currentPos = 2;
			
		assertEquals(2, m1.getMonth());
	}
	
	@Test
	public void testIncrement1() {
		m1.currentPos = 10;
		m1.increment();
		
		assertEquals(11, m1.currentPos);
	}
	
	@Test
	public void testIncrement2() {
		m1.currentPos = 10;
		assertTrue(m1.increment());
	}
	
	@Test
	public void testIncrement3() {
		m1.currentPos = 11;
		m1.increment();
		
		assertEquals(12, m1.currentPos);
	}
	
	@Test
	public void testIncrement4() {
		m1.currentPos = 11;
		assertTrue(m1.increment());
	}
	
	@Test
	public void testIncrement5() {
		m1.currentPos = 12;
		m1.increment();
		
		assertEquals(13, m1.currentPos);
	}
	
	@Test
	public void testIncrement6() {
		m1.currentPos = 12;
		assertFalse(m1.increment());
	}
	
	//访问month的私有成员，将month.y设置成null
	@Test
	public void testIsValid1() throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
		Field f = Month.class.getDeclaredField("y");
		f.setAccessible(true);
		f.set(m1, null);
		
		//y1=null; 这样能将m1.y设置成null吗?
		assertFalse(m1.isValid());
	}
	
	@Test
	public void testSetMonth1() {
		m1.setMonth(6, y2);
		
		assertEquals(6, m1.currentPos);
	}
	
	@Test
	public void testSetMonth2() throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
		m1.setMonth(6, y2);
		
		Field f = Month.class.getDeclaredField("y");
		f.setAccessible(true);
		
		assertEquals(y2, (Year)f.get(m1));
	}
	
	@Test(expected=IllegalArgumentException.class)
	public void testSetMonth3() {
		m1.setMonth(-5, y2);
	}
	
	@Test
	public void testEquals1() {
		m2 = new Month(2,y1); //1991-2
		
		assertTrue(m1.equals(m1)); 
	}
	
	@Test
	public void testEquals2() {
		assertFalse(m1.equals(m2)); //m1.y!=m2.y
	}
	
	@Test
	public void testEquals3() {
		m2 = new Month(3,y1);
		assertFalse(m1.equals(m2)); //m1.currentPos!=m2.currentPos
	}
	
	@Test
	public void testEquals4() {
		m2 = new Month(3,y2);
		assertFalse(m1.equals(m2)); //m1.currentPos!=m2.currentPos && m1.y!=m2.y
	}
	
	@Test
	public void testEquals5() {
		assertFalse(m1.equals("hello"));
	}
	
	@Test
	public void testEquals6() {
		assertFalse(m1.equals(null));
	}
	
	@Test
	public void testGetMonthSize1() throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
		assertEquals(28,m1.getMonthSize());
		
		Field f = Month.class.getDeclaredField("sizeIndex");
		f.setAccessible(true);
		assertArrayEquals(new int[]{ 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 }, (int[])f.get(m1) );
	}
	
	@Test
	public void testGetMonthSize2() throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
		assertEquals(29,m2.getMonthSize());
		
		Field f = Month.class.getDeclaredField("sizeIndex");
		f.setAccessible(true);
		assertArrayEquals(new int[]{ 31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 }, (int[])f.get(m2) );
	}
	
	@Test
	public void testGetMonthSize3() throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
		m1.currentPos = 12;
		assertEquals(31,m1.getMonthSize());
		
		Field f = Month.class.getDeclaredField("sizeIndex");
		f.setAccessible(true);
		assertArrayEquals(new int[]{ 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 }, (int[])f.get(m1) );
	}
	
}
