/**
 * 
 */
package net.mooctest;

import static org.junit.Assert.*;

import java.lang.reflect.Field;

import org.junit.Test;

public class NextdayTest {
	
	Nextday n = new Nextday();

	@Test
	public void test() throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
		Date date = new Date(6,16,1992);
		
		Date date1 = Nextday.nextDay(date);
		
		Field f = Date.class.getDeclaredField("m");
		f.setAccessible(true);
		Month m = (Month) (f.get(date1));
		assertEquals(6, m.currentPos);
		
		f = Date.class.getDeclaredField("d");
		f.setAccessible(true);
		Day d = (Day) (f.get(date1));
		assertEquals(17, d.currentPos);
		
		f = Date.class.getDeclaredField("y");
		f.setAccessible(true);
		Year y = (Year) (f.get(date1));
		assertEquals(1992, y.currentPos);
	}

}
