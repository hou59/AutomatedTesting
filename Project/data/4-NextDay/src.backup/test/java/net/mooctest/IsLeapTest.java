package net.mooctest;

import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class IsLeapTest {
	int year;
	boolean expected;
	
	public IsLeapTest(int year, boolean expected) {
		super();
		this.year = year;
		this.expected = expected;
	}
	
	@Parameters
	public static Collection dataFeed() {
		return Arrays.asList(new Object[][] {
				{1992,true},
				{-1992,false},
				{1993,false},
				{1900,false},
				{2000,true},
				{-5,true},
				{-1991, false},
				{-101, false},
				{-401, true},
				{1,false},
				{-1, true},	
				{0, true}
			});
	}
	
	@Test
	public void testIsLeap() {
		Year y = new Year(1990);
		y.currentPos = this.year;
		assertTrue(this.expected == y.isLeap());
		
	}
}
