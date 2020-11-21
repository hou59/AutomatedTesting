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
public class BinaryHeapTest {

	public ExpectedException thrown= ExpectedException.none();

	@Test(timeout=4000)
	public void testforisEmpty() {
		//new BinaryHeap();
		assertTrue(new BinaryHeap().isEmpty());
	}
	/*
	@Test(timeout=4000)
	public void testforisFull() throws Overflow
	{
		BinaryHeap a=new BinaryHeap(2);
		a.insert(2);
		a.insert(1);
		//a.insert(9);
		assertTrue(new BinaryHeap().isFull());
		
	}
	*/
	@Test(timeout=4000)
	public void testforfindmin() throws Overflow
	{
		BinaryHeap a=new BinaryHeap(2);
		a.insert(2);
		a.insert(1);
		assertEquals(1,a.findMin());
	}
	@Test(timeout=4000)
	public void testforfindmin2()throws Overflow
	{
		BinaryHeap a=new BinaryHeap(2);
		assertEquals(-1,a.findMin());
	}
	@Test(timeout=4000)
	public void testforfindmin3()throws Overflow
	{
		BinaryHeap a=new BinaryHeap();
		a.insert(8);
		a.insert(0);
		a.insert(7);
		assertEquals(0,a.findMin());
	}
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
	/*
	@Test(timeout=4000)
	public void testforwellformed() throws Overflow
	{
		BinaryHeap a=new BinaryHeap();
		a.insert(3);
		a.deleteMin();
		assertFalse(a.wellFormed());
	}
	*/
	@Test(timeout=4000)
	public void test () throws Overflow
	{
		BinaryHeap a=new BinaryHeap();
		a.insert(7);
		a.insert(8);
		a.insert(0);
		a.insert(1);
		a.deleteMin();
		assertEquals(1,a.findMin());
	}
	@Test(timeout=4000)
	public void test2()throws Overflow
	{
		BinaryHeap a=new BinaryHeap();
		a.insert(7);
		a.insert(8);
		a.insert(0);
		a.insert(1);
		assertFalse(a.isFull());
	}
	@Test(timeout=4000)
	public void test3()throws Overflow
	{
		BinaryHeap a=new BinaryHeap();
		a.insert(7);
		a.insert(8);
		a.insert(0);
		a.insert(1);
		assertFalse(a.isEmpty());
	}
	@Test(timeout=4000)
	public void test4()throws Overflow
	{
		BinaryHeap a=new BinaryHeap();
		a.insert(7);
		a.insert(8);
		a.insert(0);
		a.insert(1);
		assertTrue(a.wellFormed());
	}
	@Test(timeout=4000)
	public void test6()throws Overflow
	{
		BinaryHeap a=new BinaryHeap();
		a.insert(7);
		a.insert(8);
		a.insert(0);
		a.insert(1);
		a.makeEmpty();
		assertTrue(a.isEmpty());
	}
	@Test(timeout=4000)
	public void test7()throws Overflow
	{
		BinaryHeap a=new BinaryHeap(1);
		a.insert(7);		
		assertTrue(a.isFull());
	}
	@Test(timeout=4000)
	public void test8()
	{
		thrown.expect(Overflow.class);
		BinaryHeap a=new BinaryHeap(1);
		try {
			a.insert(7);
		} catch (Overflow e) {
			
		}
		try {
			a.insert(9);
		} catch (Overflow e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}
	@Test(timeout=4000)
	public void test9()throws Overflow
	{
		BinaryHeap a=new BinaryHeap(-1);
				
		assertFalse(a.wellFormed());
	}
	@Test(timeout=4000)
	public void test10()throws Overflow
	{
		Random r = new Random(1);
		BinaryHeap a=new BinaryHeap();
		for(int i=0;i<50;i++)
			a.insert(r.nextInt(100));
		a.buildHeap();
		a.deleteMin();
		assertTrue(a.wellFormed());
	}
}
