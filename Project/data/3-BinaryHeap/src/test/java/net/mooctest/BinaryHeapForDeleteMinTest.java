package net.mooctest;

import static org.junit.Assert.*;

import org.junit.Test;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.util.Random;

import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

public class BinaryHeapForDeleteMinTest {
	
	@Test(timeout=4000)
	public void testfordeleteMin()
	{
		BinaryHeap a=new BinaryHeap(2);
		assertEquals(-1,a.deleteMin());
	}
	@Test(timeout=4000)
	public void testfordeleteMin2() throws Overflow
	{
		BinaryHeap a=new BinaryHeap();
		a.insert(8);
		a.insert(0);
		a.insert(7);
		assertEquals(0,a.deleteMin());
	}
}
