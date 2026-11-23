// A fuzz-style test of the XRP Ledger's ledger close-time code.
//
// The code under test is xrpl::effCloseTime (and roundCloseTime, which it
// calls) from include/xrpl/ledger/LedgerTiming.h of xrpld. Consensus calls it
// to turn the close time the validators agreed on into the close time written
// in the ledger header (RCLConsensus.cpp). Both headers below are the
// unmodified upstream files, at the commit tools/build-binary.sh pins.
//
// The test takes one input (argv[1]), decodes it into a raw close time, the
// previous ledger's close time and a close-time resolution, runs the real
// code, and traps if any property below fails. A fuzzer would try inputs one
// at a time. The proof in ../proof shows that no input reaches a trap.

#include <xrpl/basics/chrono.h>        // xrpl::NetClock
#include <xrpl/ledger/LedgerTiming.h>  // xrpl::effCloseTime, kLedgerPossibleTimeResolutions

#include <cstdint>

using Seconds = std::uint32_t;  // NetClock::rep: seconds since 2000-01-01 UTC

static_assert(sizeof(xrpl::NetClock::rep) == 4);

// The code under test, with the types consensus uses (NetClock time points and
// durations). Kept out of line so that its machine code is one block that the
// proof can name.
[[gnu::noinline]] Seconds
eff_close_time(Seconds closeTime, Seconds resolution, Seconds priorCloseTime)
{
    using TimePoint = xrpl::NetClock::time_point;
    using Duration = xrpl::NetClock::duration;
    return xrpl::effCloseTime(
               TimePoint{Duration{closeTime}}, Duration{resolution}, TimePoint{Duration{priorCloseTime}})
        .time_since_epoch()
        .count();
}

// The last second at which the arithmetic of roundCloseTime cannot wrap for
// any legal resolution (it adds half of the resolution, 60 s at most), and at
// which priorCloseTime + 1 cannot wrap. NetClock counts 32-bit seconds from
// 2000-01-01, so this is 7 February 2136. Later inputs are not tested.
constexpr Seconds kHorizon = 0xFFFFFFFFu - 60u;

[[noreturn]] static inline void
fail()
{
    __builtin_trap();
}

static inline void
check(Seconds closeTime, Seconds priorCloseTime, unsigned index)
{
    // The six resolutions the protocol allows: 10, 20, 30, 60, 90, 120 s.
    Seconds const resolution =
        static_cast<Seconds>(xrpl::kLedgerPossibleTimeResolutions[index].count());

    Seconds const eff = eff_close_time(closeTime, resolution, priorCloseTime);

    // 1. A close time of zero means "no close time" and passes through.
    if (closeTime == 0)
    {
        if (eff != 0)
            fail();
        return;
    }

    // 2. A ledger closes strictly after the ledger before it.
    if (eff <= priorCloseTime)
        fail();

    // 3. The result is the instant after the previous close, or it is on a
    //    resolution boundary within half a resolution of the raw close time.
    if (eff != priorCloseTime + 1)
    {
        if (eff % resolution != 0)
            fail();
        // In 64 bits, so that the check itself cannot wrap at 2^32.
        std::uint64_t const half = resolution / 2;
        if (std::uint64_t{eff} + half < closeTime)
            fail();
        if (eff > std::uint64_t{closeTime} + half)
            fail();
    }
}

// argv[1] carries the input as 17 characters. Only the low four bits of each
// character count, so every 32-bit value can be written without a zero byte:
//   characters 0-7   close time, most significant nibble first
//   characters 8-15  previous close time
//   character  16    index of the resolution (0-5)
int
main(int argc, char** argv)
{
    if (argc != 2)
        return 0;

    auto const* s = reinterpret_cast<unsigned char const*>(argv[1]);

    Seconds closeTime = 0;
    Seconds priorCloseTime = 0;
    for (int i = 0; i < 8; ++i)
    {
        if (s[i] == 0)
            return 0;
        closeTime = (closeTime << 4) | (s[i] & 15u);
    }
    for (int i = 8; i < 16; ++i)
    {
        if (s[i] == 0)
            return 0;
        priorCloseTime = (priorCloseTime << 4) | (s[i] & 15u);
    }
    if (s[16] == 0)
        return 0;
    unsigned const index = s[16] & 15u;

    if (index > 5 || closeTime > kHorizon || priorCloseTime > kHorizon)
        return 0;

    check(closeTime, priorCloseTime, index);
    return 0;
}
