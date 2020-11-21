package net.mooctest;

import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class DayIsValidTest {
	private int m;
	private int d;
	private boolean expected;
	
	public DayIsValidTest(int m, int d, boolean expected) {
		super();
		this.m = m;
		this.d = d;
		this.expected = expected;
	}
	
	@Parameters
	public static Collection dataFeed() {
		return Arrays.asList(new Object[][] {
			{13,6,false},
			{6,1,true},
			{6,30,true},
			{6,0,false},
			{6,31,false},
			{6,16,true},
			});
	}
	
	@Test
	public void test() {
		Year y = new Year(1991);
		Month month = new Month(6,y);
		Day day = new Day(16, month);
		
		month.currentPos = this.m;
		day.currentPos = this.d;
		
		assertTrue(expected == day.isValid());
		
	}
	
}
