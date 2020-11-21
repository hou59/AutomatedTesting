package net.mooctest;

import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class MonthIsValidTest {
	protected int y;
	protected int m;
	protected boolean expected;
	
	public MonthIsValidTest(int y, int m, boolean expected) {
		super();
		this.y = y;
		this.m = m;
		this.expected = expected;
	}
	
	@Parameters
	public static Collection dataFeed() {
		return Arrays.asList(new Object[][] {
			//{null,5, false}, null不是int类型，所以需要单独处理
			{0, 5, false},
			{1991, 1, true},
			{-191, 12, true},
			{1992, 6, true},
			{2000, 0, false},
			{-5, 13, false},
			});
	}
	
	@Test
	public void test() {
		Year year = new Year(1991);
		Month month = new Month(2, year);
		
		month.currentPos = this.m;
		year.currentPos = this.y;
		
		assertTrue(expected == month.isValid());
	}
	
}
