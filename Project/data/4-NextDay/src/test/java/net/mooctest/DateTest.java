package net.mooctest;

import static org.junit.Assert.*;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;

//import java.lang.reflect.Field;

import static org.hamcrest.CoreMatchers.containsString;

import org.junit.Test;

public class DateTest {
	Date date = new Date(6, 16, 1992);
	
	@Test
	public void testIncrement1() throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
		date.increment();

//		Field day = Date.class.getDeclaredField("d");
//		day.setAccessible(true);
//		Day d = (Day) (day.get(date));
//		assertEquals(17, d.currentPos);
//		
//		Field month = Date.class.getDeclaredField("m");
//		month.setAccessible(true);
//		Month m = (Month) (month.get(date));
//		assertEquals(6, m.currentPos);
//		
//		Field year = Date.class.getDeclaredField("y");
//		year.setAccessible(true);
//		Year y = (Year) (year.get(date));
//	
//		assertEquals(1992, y.currentPos);

		
		assertEquals(17,date.getDay().currentPos);
		assertEquals(6, date.getMonth().currentPos);
		assertEquals(1992, date.getYear().currentPos);
	}
	
	@Test
	public void testIncrement2() throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
		Date date1 = new Date(6,30,1992);
		date1.increment();		
		assertEquals(1,date1.getDay().currentPos);
		assertEquals(7, date1.getMonth().currentPos);
		assertEquals(1992, date1.getYear().currentPos);
	}
	
	@Test
	public void testIncrement3() throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
		Date date1 = new Date(12,31,1992);
		date1.increment();		
		assertEquals(1,date1.getDay().currentPos);
		assertEquals(1, date1.getMonth().currentPos);
		assertEquals(1993, date1.getYear().currentPos);
	}
	
	@Test
	public void testEquals1() {
		assertFalse(date.equals(null));
	}
	
	@Test
	public void testEquals2() {
		assertFalse(date.equals("hello"));
	}
	
	@Test
	public void testEquals3() {
		Date date1 = new Date(7, 16, 1992);
		assertFalse(date.equals(date1));
	}
	
	@Test
	public void testEquals4() {
		Date date1 = new Date(6, 17, 1992);
		assertFalse(date.equals(date1));
	}
	
	@Test
	public void testEquals5() {
		Date date1 = new Date(6, 16, 1991);
		assertFalse(date.equals(date1));
	}
	
	@Test
	public void testEquals6() {
		Date date1 = new Date(6, 16, 1992);
		assertTrue(date.equals(date1));
	}
	

	@Test
	public void testToString() {
		String actual = date.toString();
		
		assertEquals("6/16/1992", actual);
	}
	
	@Test
	public void testPrintDate() {
		 
	    final ByteArrayOutputStream outContent = new ByteArrayOutputStream();
	    System.setOut(new PrintStream(outContent));
	    
	    
	    date.printDate();
	 
	    
	    assertThat(outContent.toString(), containsString("6/16/1992"));
	}
}
