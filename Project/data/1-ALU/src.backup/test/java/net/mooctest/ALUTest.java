package net.mooctest;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.util.Random;

import org.junit.Test;

public class ALUTest {

	@Test(timeout = 4000)
	public void test() {
		ALU alu = new ALU();
	}

	@Test(timeout = 4000)
	public void test00() throws Throwable {
		ALU aLU0 = new ALU();
		aLU0.normalize("-");
	}

	@Test(timeout = 4000)
	public void test01() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.integerSubtraction("", "", (-1));
			fail("Expecting exception: StringIndexOutOfBoundsException");
		} catch (StringIndexOutOfBoundsException e) {
//			verifyException("java.lang.AbstractStringBuilder", e);
		}
	}

	@Test(timeout = 4000)
	public void test02() throws Throwable {
		ALU aLU0 = new ALU();
		aLU0.negation(")");
	}

	@Test(timeout = 4000)
	public void test03() throws Throwable {
		ALU aLU0 = new ALU();
		aLU0.floatTrueValue("d", 0, (-1));
	}

	@Test(timeout = 4000)
	public void test04() throws Throwable {
		ALU aLU0 = new ALU();
		aLU0.ieee754("", 65);
	}

	@Test(timeout = 4000)
	public void test05() throws Throwable {
		ALU aLU0 = new ALU();
		aLU0.floatRepresentation("0", 1, 0);
	}

	@Test(timeout = 4000)
	public void test06() throws Throwable {
		ALU aLU0 = new ALU();
		aLU0.floatRepresentation("-2", 0, 0);
	}

	@Test(timeout = 4000)
	public void test07() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.floatRepresentation("$", 0, 0);
			fail("Expecting exception: NumberFormatException");
		} catch (NumberFormatException e) {
//			verifyException("java.lang.NumberFormatException", e);
		}
	}

	@Test(timeout = 4000)
	public void test08() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.integerRepresentation("+", 0);
			fail("Expecting exception: NumberFormatException");
		} catch (NumberFormatException e) {
//			verifyException("java.lang.NumberFormatException", e);
		}
	}

	@Test(timeout = 4000)
	public void test09() throws Throwable {
		ALU aLU0 = new ALU();
		aLU0.negation("");
	}

	@Test(timeout = 4000)
	public void test10() throws Throwable {
		ALU aLU0 = new ALU();
		aLU0.leftShift("", 0);
	}

	@Test(timeout = 4000)
	public void test11() throws Throwable {
		ALU aLU0 = new ALU();
		aLU0.integerSubtraction("n", "n", 4);
	}

	@Test(timeout = 4000)
	public void test12() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.oneAdder((String) null);
			fail("Expecting exception: NullPointerException");
		} catch (NullPointerException e) {
//			verifyException("net.mooctest.ALU", e);
		}
	}

	@Test(timeout = 4000)
	public void test13() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.normalize((String) null);
			fail("Expecting exception: NullPointerException");
		} catch (NullPointerException e) {
//			verifyException("net.mooctest.ALU", e);
		}
	}

	@Test(timeout = 4000)
	public void test14() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.negation((String) null);
			fail("Expecting exception: NullPointerException");
		} catch (NullPointerException e) {
//			verifyException("net.mooctest.ALU", e);
		}
	}

	@Test(timeout = 4000)
	public void test15() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.leftShift("", 1);
			fail("Expecting exception: StringIndexOutOfBoundsException");
		} catch (StringIndexOutOfBoundsException e) {
		}
	}

	@Test(timeout = 4000)
	public void test16() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.leftShift((String) null, 0);
			fail("Expecting exception: NullPointerException");
		} catch (NullPointerException e) {
//			verifyException("net.mooctest.ALU", e);
		}
	}

	@Test(timeout = 4000)
	public void test17() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.integerTrueValue((String) null);
			fail("Expecting exception: NullPointerException");
		} catch (NullPointerException e) {
//			verifyException("net.mooctest.ALU", e);
		}
	}

	@Test(timeout = 4000)
	public void test18() throws Throwable {
		ALU aLU0 = new ALU();
		aLU0.integerSubtraction("k", "k", 1112);
	}

	@Test(timeout = 4000)
	public void test19() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.integerRepresentation("", 0);
			fail("Expecting exception: StringIndexOutOfBoundsException");
		} catch (StringIndexOutOfBoundsException e) {
		}
	}

	@Test(timeout = 4000)
	public void test20() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.integerRepresentation((String) null, 0);
			fail("Expecting exception: NullPointerException");
		} catch (NullPointerException e) {
//			verifyException("net.mooctest.ALU", e);
		}
	}

	@Test(timeout = 4000)
	public void test21() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.ieee754("f", 32);
			fail("Expecting exception: NumberFormatException");
		} catch (NumberFormatException e) {
//			verifyException("java.lang.NumberFormatException", e);
		}
	}

	@Test(timeout = 4000)
	public void test22() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.floatTrueValue((String) null, 0, 0);
			fail("Expecting exception: NullPointerException");
		} catch (NullPointerException e) {
//			verifyException("net.mooctest.ALU", e);
		}
	}

	@Test(timeout = 4000)
	public void test23() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.floatRepresentation("", 0, 0);
			fail("Expecting exception: StringIndexOutOfBoundsException");
		} catch (StringIndexOutOfBoundsException e) {
		}
	}

	@Test(timeout = 4000)
	public void test24() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.floatRepresentation((String) null, 0, 0);
			fail("Expecting exception: NullPointerException");
		} catch (NullPointerException e) {
//			verifyException("net.mooctest.ALU", e);
		}
	}

	@Test(timeout = 4000)
	public void test25() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.claAdder("5szk", (String) null, 'N');
			fail("Expecting exception: NullPointerException");
		} catch (NullPointerException e) {
//			verifyException("net.mooctest.ALU", e);
		}
	}

	@Test(timeout = 4000)
	public void test26() throws Throwable {
		ALU aLU0 = new ALU();
		aLU0.adder("o", "o", 'y', 1112);
	}

	@Test(timeout = 4000)
	public void test27() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.adder((String) null, (String) null, 'L', 0);
			fail("Expecting exception: NullPointerException");
		} catch (NullPointerException e) {
		}
	}

	@Test(timeout = 4000)
	public void test28() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.fullAdder('', '', '');
		assertEquals("01", string0);
	}

	@Test(timeout = 4000)
	public void test29() throws Throwable {
		ALU aLU0 = new ALU();
		char char0 = aLU0.xorGate('S', 'S');
		assertEquals('0', char0);
	}

	@Test(timeout = 4000)
	public void test30() throws Throwable {
		ALU aLU0 = new ALU();
		char char0 = aLU0.xorGate('=', 'C');
		assertEquals('1', char0);
	}

	@Test(timeout = 4000)
	public void test31() throws Throwable {
		ALU aLU0 = new ALU();
		char char0 = aLU0.andGate('N', 'N');
		assertEquals('0', char0);
	}

	@Test(timeout = 4000)
	public void test32() throws Throwable {
		ALU aLU0 = new ALU();
		char char0 = aLU0.andGate('1', '8');
		assertEquals('0', char0);
	}

	@Test(timeout = 4000)
	public void test33() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.claAdder("MK:P", "MK:P", 'k');
		assertEquals("00001", string0);
	}

	@Test(timeout = 4000)
	public void test34() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.claAdder("", "", 'k');
			fail("Expecting exception: StringIndexOutOfBoundsException");
		} catch (StringIndexOutOfBoundsException e) {
		}
	}

	@Test(timeout = 4000)
	public void test35() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.oneAdder("O");
		assertEquals("01", string0);
	}

	@Test(timeout = 4000)
	public void test36() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.negation("0");
		assertEquals("1", string0);
	}

	@Test(timeout = 4000)
	public void test37() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.integerRepresentation("0", 1);
		assertEquals("0", string0);
	}

	@Test(timeout = 4000)
	public void test38() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.integerRepresentation("1", 0);
		assertEquals("1", string0);
	}

	@Test(timeout = 4000)
	public void test39() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.integerRepresentation("0", 0);
		assertEquals("", string0);
	}

	@Test(timeout = 4000)
	public void test40() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.integerRepresentation("-", 0);
			fail("Expecting exception: NumberFormatException");
		} catch (NumberFormatException e) {
//			verifyException("java.lang.NumberFormatException", e);
		}
	}

	@Test(timeout = 4000)
	public void test41() throws Throwable {
		ALU aLU0 = new ALU();
		int int0 = aLU0.normalize("0");
		assertEquals(1, int0);
	}

	@Test(timeout = 4000)
	public void test42() throws Throwable {
		ALU aLU0 = new ALU();
		int int0 = aLU0.normalize("");
		assertEquals(0, int0);
	}

	@Test(timeout = 4000)
	public void test43() throws Throwable {
		ALU aLU0 = new ALU();
		int int0 = aLU0.normalize("g");
		assertEquals(1, int0);
	}

	@Test(timeout = 4000)
	public void test44() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.adder("}V16;j]}", "I", 's', 5);
		assertEquals("011111", string0);
	}

	@Test(timeout = 4000)
	public void test45() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.adder("I", "r", '2', 9);
		assertEquals("0000000001", string0);
	}

	@Test(timeout = 4000)
	public void test46() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.floatTrueValue("00000000000000000000000000", 8, 0);
		assertEquals("0.0", string0);
	}

	@Test(timeout = 4000)
	public void test47() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.adder("1", "1", '\"', 2);
			fail("Expecting exception: StringIndexOutOfBoundsException");
		} catch (StringIndexOutOfBoundsException e) {
//			verifyException("java.lang.AbstractStringBuilder", e);
		}
	}

	@Test(timeout = 4000)
	public void test48() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.oneAdder("");
		assertEquals("1", string0);
	}

	@Test(timeout = 4000)
	public void test49() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.leftShift("f0V", 1);
		assertEquals("0V0", string0);
	}

	@Test(timeout = 4000)
	public void test50() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.floatTrueValue("QfVuZ", 4, 2);
			fail("Expecting exception: StringIndexOutOfBoundsException");
		} catch (StringIndexOutOfBoundsException e) {
		}
	}

	@Test(timeout = 4000)
	public void test51() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.floatTrueValue("QfVuZ", 4, 0);
		assertEquals("1.0", string0);
	}

	@Test(timeout = 4000)
	public void test52() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.floatTrueValue("00", 0, 0);
		assertEquals("NaN", string0);
	}

	@Test(timeout = 4000)
	public void test53() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.floatTrueValue("1", 0, 0);
		assertEquals("-Inf", string0);
	}

	@Test(timeout = 4000)
	public void test54() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.integerTrueValue("gz");
		assertEquals("-36", string0);
	}

	@Test(timeout = 4000)
	public void test55() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.ieee754("", 64);
			fail("Expecting exception: StringIndexOutOfBoundsException");
		} catch (StringIndexOutOfBoundsException e) {
		}
	}

	@Test(timeout = 4000)
	public void test56() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.ieee754("", 0);
		assertEquals("", string0);
	}

	@Test(timeout = 4000)
	public void test57() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.floatRepresentation("1", 0, 1);
		assertEquals("NaN", string0);
	}

	@Test(timeout = 4000)
	public void test58() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.floatRepresentation("4.0", 0, 0);
		assertEquals("NaN", string0);
	}

	@Test(timeout = 4000)
	public void test59() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.floatRepresentation("0", 0, 1);
		assertEquals("00", string0);
	}

	@Test(timeout = 4000)
	public void test60() throws Throwable {
		ALU aLU0 = new ALU();
		String string0 = aLU0.floatRepresentation("47", 32, 0);
		assertEquals("010000000000000000000000000000011", string0);
	}

	@Test(timeout = 4000)
	public void test61() throws Throwable {
		ALU aLU0 = new ALU();
		try {
			aLU0.integerSubtraction((String) null, (String) null, 0);
			fail("Expecting exception: NullPointerException");
		} catch (NullPointerException e) {
//			verifyException("net.mooctest.ALU", e);
		}
	}

	static class ALU2 extends ALU{
		/**
		 * 生成十进制整数的二进制补码表示�?? 例：integerRepresentation("9", 8)
		 *
		 * @param number
		 *            十进制整数�?�若为负数；则第�?位为�?-”；若为正数�? 0，则无符号位
		 * @param length
		 *            二进制补码表示的长度
		 * @return number的二进制补码表示，长度为length
		 */
		@Override
		public String integerRepresentation(String number, int length) {
			StringBuilder result = new StringBuilder();
			String tmpNum;
			boolean isMinus;
			if (number.charAt(0) == '-') {
				isMinus = true;
				tmpNum = number.substring(1);
			} else {
				isMinus = false;
				tmpNum = number;
			}
			// 下面对绝对�?�进行处�?
			int n = Integer.valueOf(tmpNum);
			while (n >= 1) {
				result.insert(0, String.valueOf(n % 2));
				n = (n - n % 2) / 2;
			}
			// 若是负数,取反加一
			if (isMinus) {
				result = new StringBuilder(oneAdder(negation(result.toString())).substring(1, result.length() + 1));
			}
			// 补全�? length �?
			while (result.length() < length) {
				if (isMinus) {
					result.insert(0, "1");
				} else {
					result.insert(0, "0");
				}
			}
			return result.toString();
		}

		/**
		 * 生成十进制浮点数的二进制表示�? �?要�?�虑 0、反规格化�?�正负无穷（�?+Inf”和�?-Inf”）�? NaN等因素，具体借鉴 IEEE 754�?
		 * 舍入策略为向0舍入�? 例：floatRepresentation("11.375", 8, 11)
		 *
		 * @param number
		 *            十进制浮点数，包含小数点。若为负数；则第�?位为�?-”；若为正数�? 0，则无符号位
		 * @param eLength
		 *            指数的长度，取�?�大于等�? 4
		 * @param sLength
		 *            尾数的长度，取�?�大于等�? 4
		 * @return number的二进制表示，长度为 1+eLength+sLength。从左向右，依次为符号�?�指数（移码表示）�?�尾数（首位隐藏�?
		 */
		@Override
		public String floatRepresentation(String number, int eLength, int sLength) {
			StringBuilder result = new StringBuilder();
			int n;
			// 注意:以小数点分隔,必须加双右斜�?
			String strs[] = number.split("\\.");
			if (strs[0].charAt(0) != '-') {
				result.insert(0, "0");
				n = Integer.valueOf(strs[0]);
			} else {
				result.insert(0, "1");
				n = Integer.valueOf(strs[0].substring(1));
			}
			// 判断是否�?0?若是零直接返�?
			boolean isZero = true;
			for (String str : strs) {
				if (Integer.valueOf(str) != 0) {
					isZero = false;
					break;
				}
			}
			if (isZero) {
				while (result.length() < 1 + eLength + sLength) {
					result.append("0");
				}
				return result.toString();
			}
			// 生成整数部分的二进制表示
			StringBuilder beforeDot = new StringBuilder();
			if (n != 0) {
				while (n >= 1) {
					beforeDot.insert(0, String.valueOf(n % 2));
					n = (n - n % 2) / 2;
				}
			}
			// 生成小数部分的二进制表示(若有)
			StringBuilder afterDot = new StringBuilder();
			if (strs.length > 1) {
				float m = (float) (Integer.valueOf(strs[1])) * (float) Math.pow(10, -strs[1].length());
				if (m == 0) {
					afterDot = new StringBuilder(allZeroWithLength(eLength + sLength + 1));
				} else {
					// �?后一�?1是为了能�?后向0舍入
					do {
						if ((m *= 2) >= 1) {
							m -= 1;
							afterDot.append("1");
						} else {
							afterDot.append("0");
						}
					} while (m != 1 && beforeDot.length() + afterDot.length() <= eLength + sLength + 1 + 1);
				}
			}
			// 是否要规格化?
			// 拼接整数和小�?,且算出指�?
			int e;
			String exponent;
			int bias = (int) Math.pow(2, eLength - 1) - 1;
			if (beforeDot.toString().equals("")) {
				e = normalize(afterDot.toString());
				if (bias - e < 0) {
					// 反规格化
					System.out.println(bias - e);
					System.out.println(afterDot);
					afterDot = new StringBuilder(afterDot.substring(normalize(afterDot.toString()) - 1));
					while (afterDot.length() < sLength) {
						afterDot.append("0");
					}
					return result + allZeroWithLength(eLength) + afterDot;
				}
				exponent = integerRepresentation((bias - e) + "", eLength);
			} else {
				e = beforeDot.length() - 1;
				exponent = integerRepresentation((bias + e) + "", eLength);
			}
			if (strs.length > 1) {
				if (beforeDot.toString().equals("")) {
					afterDot = new StringBuilder(leftShift(afterDot.toString(), e));
					result.append(exponent).append(afterDot);
				} else {
					result.append(exponent).append(beforeDot.substring(1)).append(afterDot);
				}
			} else {
				result.append(exponent).append(beforeDot.toString().equals("") ? "" : beforeDot.substring(1));
			}
			if (result.length() > 1 + eLength + sLength) {
				result = new StringBuilder(result.substring(0, 1 + eLength + sLength));
			}
			// +-Inf,NaN
			if (exponent.equals(allOneWithLength(exponent.length()))) {
				if (result.substring(1 + eLength, result.length()).equals(allZeroWithLength(1 + eLength + sLength))) {
					return result.charAt(0) == '0' ? "+Inf" : "-Inf";
				} else {
					return "NaN";
				}
			}
			return result.toString();
		}

		/**
		 * 生成十进制浮点数的IEEE 754表示，要求调用floatRepresentation(String, int, int)实现�?
		 * 例：ieee754("11.375", 32)
		 *
		 * @param number
		 *            十进制浮点数，包含小数点。若为负数；则第�?位为�?-”；若为正数�? 0，则无符号位
		 * @param length
		 *            二进制表示的长度，为32�?64
		 * @return number的IEEE 754表示，长度为length。从左向右，依次为符号�?�指数（移码表示）�?�尾数（首位隐藏�?
		 */
		@Override
		public String ieee754(String number, int length) {
			if (length == 32) {
				return floatRepresentation(number, 8, 23);
			} else if (length == 64) {
				return floatRepresentation(number, 11, 52);
			} else {
				return "";
			}
		}


		/**
		 * 左移操作�? 例：leftShift("00001001", 2)
		 *
		 * @param operand
		 *            二进制表示的操作�?
		 * @param n
		 *            左移的位�?
		 * @return operand左移n位的结果
		 */
		@Override
		public String leftShift(String operand, int n) {
			StringBuilder result = new StringBuilder(operand.substring(n, operand.length()));
			while (result.length() < operand.length()) {
				result.append("0");
			}
			return result.toString();
		}

		// 返回长为n的全0�?
		private String allZeroWithLength(int n) {
			StringBuilder result = new StringBuilder();
			while (result.length() < n) {
				result.append("0");
			}
			return result.toString();
		}

		// 返回长为n的全1�?
		private String allOneWithLength(int n) {
			StringBuilder result = new StringBuilder();
			while (result.length() < n) {
				result.append("1");
			}
			return result.toString();
		}


		// 规格化一个数,返回值为�?要在指数上加的数�?(可正可负)
		@Override
		public int normalize(String num) {
			int i = 0;
			char c = '0';
			while (i < num.length()) {
				if (num.charAt(i) == c) {
					c = num.charAt(i);
					i++;
				} else {
					i++;
					break;
				}
			}
			return i;
		}
	}

	@Test
	public void manualTest(){
		ALU alu = new ALU();
		ALU2 alu2 = new ALU2();
		assertEquals(alu2.ieee754("3.1415926", 32), alu.ieee754("3.1415926", 32));
		assertEquals(alu2.ieee754("-3.00", 64), alu.ieee754("-3.00", 64));
		assertEquals(alu2.ieee754("0.0", 64), alu.ieee754("0.0", 64));
		assertEquals(alu2.ieee754("0.233", 64), alu.ieee754("0.233", 64));
		Random rand = new Random();
//		for(int i = 0;i < 1000;i++){
//			float a = rand.nextFloat() * 1000;
//			assertEquals(alu2.ieee754(String.valueOf(a), 64),alu.ieee754(String.valueOf(a), 64));
//		}

		assertEquals(alu2.ieee754("233", 64), alu.ieee754("233", 64));
		assertEquals(alu2.ieee754("3.1415926", 0), alu.ieee754("3.1415926", 0));
//
		assertEquals(alu2.floatRepresentation("0.01", 4, 5), alu.floatRepresentation("0.01", 4, 5));

		OutputStream os = new ByteArrayOutputStream();
		PrintStream ps = new PrintStream(os);
		System.setOut(ps);
		assertEquals(alu2.floatRepresentation("0.01", 2, 5), alu.floatRepresentation("0.01", 2, 5));
		ps.flush();
		assertTrue(os.toString().trim().contains("-6"));
		assertFalse(os.toString().trim().contains("-5"));
		assertTrue(os.toString().trim().contains("0000001010"));
		assertFalse(os.toString().trim().contains("101001010"));

		assertEquals("NaN", alu.floatRepresentation(String.valueOf(Integer.MAX_VALUE), 2, 10));
		assertEquals("+Inf", alu.floatRepresentation("2", -1, 1));

	}

}
