import Promise from 'bluebird';
import crypto from 'crypto';
import { BigInteger as BigInt } from 'jsbn';

Promise.promisifyAll(crypto);

export const BIG_TWO = new BigInt('2');

/**
 * Trims a BigInt to a specific length.
 * @param {BigInt} bi BigInt to be trimmed.
 * @param {number} bits Number of bits in the output.
 * @returns {BigInt}
 */
function trimBigInt(bi, bits) {
  const trimLength = bi.bitLength() - bits;
  return trimLength > 0 ? bi.shiftRight(trimLength) : bi;
}

/**
 * Returns a random BigInt with the given amount of bits.
 * @param {number} bits Number of bits in the output.
 * @returns {BigInt}
 */
export async function getRandomNbitBigIntAsync(bits) {
  // Generate random bytes with the length of the range
  const buf = await crypto.randomBytesAsync(Math.ceil(bits / 8));
  const bi = new BigInt(buf.toString('hex'), 16);

  // Trim the result and then ensure that the highest bit is set
  return trimBigInt(bi, bits).setBit(bits - 1);
}

/**
 * Returns a random BigInt in the given range.
 * @param {BigInt} min Minimum value (included).
 * @param {BigInt} max Maximum value (excluded).
 * @returns {BigInt}
 */
export async function getRandomBigIntAsync(min, max) {
  const range = max.subtract(min).subtract(BigInt.ONE);

  let bi;
  do {
    // Generate random bytes with the length of the range
    const buf = await crypto.randomBytesAsync(Math.ceil(range.bitLength() / 8));

    // Offset the result by the minimum value
    bi = new BigInt(buf.toString('hex'), 16).add(min);
  } while (bi.compareTo(max) >= 0);

  // Return the result which satisfies the given range
  return bi;
}

/**
 * Returns a random prime BigInt value.
 * @param {number} bits Number of bits in the output.
 * @returns {BigInt}
 */
export async function getBigPrimeAsync(bits) {
  // Generate a random odd number with the given length
  let bi = (await getRandomNbitBigIntAsync(bits)).or(BigInt.ONE);

  while (!bi.isProbablePrime()) {
    bi = bi.add(BIG_TWO);
  }

  // Trim the result and then ensure that the highest bit is set
  return trimBigInt(bi, bits).setBit(bits - 1);
}

/**
 * Parses a BigInt.
 * @param {BigInt|string|number} obj Object to be parsed.
 * @returns {?BigInt}
 */
export function parseBigInt(obj) {
  if (obj === undefined) return null;

  return obj instanceof Object ? obj : new BigInt(`${obj}`);
}


class EncryptedValue {
	constructor(a, b) {
	  this.a = a;
	  this.b = b;
	}
  
	/**
	 * Performs homomorphic multiplication of the current and the given value.
	 */
	multiply(encryptedValue) {
	  return new EncryptedValue(
		this.a.multiply(encryptedValue.a),
		this.b.multiply(encryptedValue.b)
	  );
	}
  }
  

class DecryptedValue {
	constructor(m) {
	  switch (typeof m) {
		case 'string':
		  this.bi = new BigInt(new Buffer(m).toString('hex'), 16);
		  break;
		case 'number':
		  this.bi = new BigInt(`${m}`);
		  break;
		default:
		  this.bi = m;
	  }
	}
  
	toString() {
	  return new Buffer(this.bi.toByteArray()).toString();
	}
  }

  
/**
 * Provides methods for the ElGamal cryptosystem.
 */
class ElGamal {
  /**
   * Safe prime number.
   */
  p;

  /**
   * Generator.
   */
  g;

  /**
   * Public key.
   */
  y;

  /**
   * Private key.
   */
  x;

  static async generateAsync(primeBits = 2048) {
    let q;
    let p;
    do {
      q = await Utils.getBigPrimeAsync(primeBits - 1);
      p = q.shiftLeft(1).add(BigInt.ONE);
    } while (!p.isProbablePrime()); // Ensure that p is a prime

    let g;
    do {
      // Avoid g=2 because of Bleichenbacher's attack
      g = await Utils.getRandomBigIntAsync(new BigInt('3'), p);
    } while (
      g.modPowInt(2, p).equals(BigInt.ONE) ||
      g.modPow(q, p).equals(BigInt.ONE) ||
      // g|p-1
      p.subtract(BigInt.ONE).remainder(g).equals(BigInt.ZERO) ||
      // g^(-1)|p-1 (evades Khadir's attack)
      p.subtract(BigInt.ONE).remainder(g.modInverse(p)).equals(BigInt.ZERO)
    );

    // Generate private key
    const x = await Utils.getRandomBigIntAsync(
      Utils.BIG_TWO,
      p.subtract(BigInt.ONE)
    );

    // Generate public key
    const y = g.modPow(x, p);

    return new ElGamal(p, g, y, x);
  }

  /**
   * Creates a new ElGamal instance.
   * @param p Safe prime number.
   * @param g Generator.
   * @param y Public key.
   * @param x Private key.
   */
  constructor(p, g, y, x) {
    this.p = Utils.parseBigInt(p);
    this.g = Utils.parseBigInt(g);
    this.y = Utils.parseBigInt(y);
    this.x = Utils.parseBigInt(x);
  }

  /**
   * Encrypts a message.
   */
  async encryptAsync(m, k) {
    const tmpKey = Utils.parseBigInt(k) || await Utils.getRandomBigIntAsync(
      BigInt.ONE,
      this.p.subtract(BigInt.ONE)
    );
    const mBi = new DecryptedValue(m).bi;
    const p = this.p;

    const a = this.g.modPow(tmpKey, p);
    const b = this.y.modPow(tmpKey, p).multiply(mBi).remainder(p);

    return new EncryptedValue(a, b);
  }

  /**
   * Decrypts a message.
   */
  async decryptAsync(m) {
    // TODO: Use a custom error object
    if (!this.x) throw new Errors.MissingPrivateKeyError();

    const p = this.p;
    const r = await Utils.getRandomBigIntAsync(
      Utils.BIG_TWO,
      this.p.subtract(BigInt.ONE)
    );

    const aBlind = this.g.modPow(r, p).multiply(m.a).remainder(p);
    const ax = aBlind.modPow(this.x, p);

    const plaintextBlind = ax.modInverse(p).multiply(m.b).remainder(p);
    const plaintext = this.y.modPow(r, p).multiply(plaintextBlind).remainder(p);

    return new DecryptedValue(plaintext);
  }
}


const egCustom = new ElGamal(17, 3, 13, 4);

const secret = 'The quick brown fox jumps over the lazy dog';
const encrypted = await eg.encryptAsync(secret);
const decrypted = await eg.decryptAsync(encrypted);

console.log(decrypted.toString() === secret); // true