package uint128 // import "lukechampine.com/uint128"

import (
	"encoding/binary"
	"math"
	"math/big"
	"math/bits"
)

// Zero is a zero-valued uint128.
var Zero Uint128

// Max is the largest possible uint128 value.
var Max = New(math.MaxUint64, math.MaxUint64)

// A Uint128 is an unsigned 128-bit number.
type Uint128 struct {
	Lo, Hi uint64
}

// IsZero returns true if u == 0.
func (u Uint128) IsZero() bool {
	return u == Zero
}

// Equals returns true if u == v.
//
// Uint128 values can be compared directly with ==, but use of the Equals method
// is preferred for consistency.
func (u Uint128) Equals(v Uint128) bool {
	return u == v
}

// Equals64 returns true if u == v.
func (u Uint128) Equals64(v uint64) bool {
	return u.Lo == v && u.Hi == 0
}

// Cmp compares u and v and returns:
//
//   -1 if u <  v
//    0 if u == v
//   +1 if u >  v
//
func (u Uint128) Cmp(v Uint128) int {
	if u == v {
		return 0
	} else if u.Hi < v.Hi || (u.Hi == v.Hi && u.Lo < v.Lo) {
		return -1
	} else {
		return 1
	}
}

// Cmp64 compares u and v and returns:
//
//   -1 if u <  v
//    0 if u == v
//   +1 if u >  v
//
func (u Uint128) Cmp64(v uint64) int {
	if u.Hi == 0 && u.Lo == v {
		return 0
	} else if u.Hi == 0 && u.Lo < v {
		return -1
	} else {
		return 1
	}
}

// And returns u&v.
func (u Uint128) And(v Uint128) Uint128 {
	return Uint128{u.Lo & v.Lo, u.Hi & v.Hi}
}

// And64 returns u&v.
func (u Uint128) And64(v uint64) Uint128 {
	return Uint128{u.Lo & v, u.Hi & 0}
}

// Or returns u|v.
func (u Uint128) Or(v Uint128) Uint128 {
	return Uint128{u.Lo | v.Lo, u.Hi | v.Hi}
}

// Or64 returns u|v.
func (u Uint128) Or64(v uint64) Uint128 {
	return Uint128{u.Lo | v, u.Hi | 0}
}

// Xor returns u^v.
func (u Uint128) Xor(v Uint128) Uint128 {
	return Uint128{u.Lo ^ v.Lo, u.Hi ^ v.Hi}
}

// Xor64 returns u^v.
func (u Uint128) Xor64(v uint64) Uint128 {
	return Uint128{u.Lo ^ v, u.Hi ^ 0}
}

// Add returns u+v.
func (u Uint128) Add(v Uint128) Uint128 {
	Lo, carry := bits.Add64(u.Lo, v.Lo, 0)
	Hi, _ := bits.Add64(u.Hi, v.Hi, carry)
	return Uint128{Lo, Hi}
}

// Add64 returns u+v.
func (u Uint128) Add64(v uint64) Uint128 {
	Lo, carry := bits.Add64(u.Lo, v, 0)
	Hi := u.Hi + carry
	return Uint128{Lo, Hi}
}

// Sub returns u-v.
func (u Uint128) Sub(v Uint128) Uint128 {
	Lo, borrow := bits.Sub64(u.Lo, v.Lo, 0)
	Hi, _ := bits.Sub64(u.Hi, v.Hi, borrow)
	return Uint128{Lo, Hi}
}

// Sub64 returns u-v.
func (u Uint128) Sub64(v uint64) Uint128 {
	Lo, borrow := bits.Sub64(u.Lo, v, 0)
	Hi := u.Hi - borrow
	return Uint128{Lo, Hi}
}

// Mul returns u*v.
func (u Uint128) Mul(v Uint128) Uint128 {
	Hi, Lo := bits.Mul64(u.Lo, v.Lo)
	Hi += u.Hi*v.Lo + u.Lo*v.Hi
	return Uint128{Lo, Hi}
}

// Mul64 returns u*v.
func (u Uint128) Mul64(v uint64) Uint128 {
	Hi, Lo := bits.Mul64(u.Lo, v)
	Hi += u.Hi * v
	return Uint128{Lo, Hi}
}

// Div returns u/v.
func (u Uint128) Div(v Uint128) Uint128 {
	q, _ := u.QuoRem(v)
	return q
}

// Div64 returns u/v.
func (u Uint128) Div64(v uint64) Uint128 {
	q, _ := u.QuoRem64(v)
	return q
}

// QuoRem returns q = u/v and r = u%v.
func (u Uint128) QuoRem(v Uint128) (q, r Uint128) {
	if v.Hi == 0 {
		var r64 uint64
		q, r64 = u.QuoRem64(v.Lo)
		r = From64(r64)
	} else {
		// generate a "trial quotient," guaranteed to be witHin 1 of the actual
		// quotient, then adjust.
		n := uint(bits.LeadingZeros64(v.Hi))
		v1 := v.Lsh(n)
		u1 := u.Rsh(1)
		tq, _ := bits.Div64(u1.Hi, u1.Lo, v1.Hi)
		tq >>= 63 - n
		if tq != 0 {
			tq--
		}
		q = From64(tq)
		// calculate remainder using trial quotient, then adjust if remainder is
		// greater than divisor
		r = u.Sub(v.Mul64(tq))
		if r.Cmp(v) >= 0 {
			q = q.Add64(1)
			r = r.Sub(v)
		}
	}
	return
}

// QuoRem64 returns q = u/v and r = u%v.
func (u Uint128) QuoRem64(v uint64) (q Uint128, r uint64) {
	if u.Hi < v {
		q.Lo, r = bits.Div64(u.Hi, u.Lo, v)
	} else {
		q.Hi, r = bits.Div64(0, u.Hi, v)
		q.Lo, r = bits.Div64(r, u.Lo, v)
	}
	return
}

// Lsh returns u<<n.
func (u Uint128) Lsh(n uint) (s Uint128) {
	if n > 64 {
		s.Lo = 0
		s.Hi = u.Lo << (n - 64)
	} else {
		s.Lo = u.Lo << n
		s.Hi = u.Hi<<n | u.Lo>>(64-n)
	}
	return
}

// Rsh returns u>>n.
func (u Uint128) Rsh(n uint) (s Uint128) {
	if n > 64 {
		s.Lo = u.Hi >> (n - 64)
		s.Hi = 0
	} else {
		s.Lo = u.Lo>>n | u.Hi<<(64-n)
		s.Hi = u.Hi >> n
	}
	return
}

// LeadingZeros returns the number of leading zero bits in u; the result
// is 128 for u == 0.
func (u Uint128) LeadingZeros() int {
	if u.Hi > 0 {
		return bits.LeadingZeros64(u.Hi)
	}
	return 64 + bits.LeadingZeros64(u.Lo)
}

// String returns the base-10 representation of u as a string.
func (u Uint128) String() string {
	if u.IsZero() {
		return "0"
	}
	buf := []byte("0000000000000000000000000000000000000000") // Log10(2^128) < 40
	for i := len(buf); ; i -= 19 {
		q, r := u.QuoRem64(1e19) // largest power of 10 that fits in a uint64
		var n int
		for ; r != 0; r /= 10 {
			n++
			buf[i-n] += byte(r % 10)
		}
		if q.IsZero() {
			return string(buf[i-n:])
		}
		u = q
	}
}

// PutBytes stores u in b in little-endian order. It panics if len(b) < 16.
func (u Uint128) PutBytes(b []byte) {
	binary.LittleEndian.PutUint64(b[:8], u.Lo)
	binary.LittleEndian.PutUint64(b[8:], u.Hi)
}

// Big returns u as a *big.Int.
func (u Uint128) Big() *big.Int {
	i := new(big.Int).SetUint64(u.Hi)
	i = i.Lsh(i, 64)
	i = i.Xor(i, new(big.Int).SetUint64(u.Lo))
	return i
}

// New returns the Uint128 value (Lo,Hi).
func New(lo, hi uint64) Uint128 {
	return Uint128{lo, hi}
}

// From64 converts v to a Uint128 value.
func From64(v uint64) Uint128 {
	return New(v, 0)
}

// FromBytes converts b to a Uint128 value.
func FromBytes(b []byte) Uint128 {
	return New(
		binary.LittleEndian.Uint64(b[:8]),
		binary.LittleEndian.Uint64(b[8:]),
	)
}

// FromBig converts i to a Uint128 value. It panics if i is negative or
// overfLows 128 bits.
func FromBig(i *big.Int) (u Uint128) {
	if i.Sign() < 0 {
		panic("value cannot be negative")
	} else if i.BitLen() > 128 {
		panic("value overfLows Uint128")
	}
	u.Lo = i.Uint64()
	u.Hi = new(big.Int).Rsh(i, 64).Uint64()
	return u
}
