pragma solidity =0.8.19;

import {Math} from "@src/util/Math.sol";

import "@forge-std/Test.sol";

import {MockDynamicRateLimited} from "@test/mock/MockDynamicRateLimited.sol";
import {DynamicRateLimitLibrary, RateLimit} from "@src/lib/DynamicRateLimitLibrary.sol";

contract UnitTestDynamicRateLimited is Test {
    using DynamicRateLimitLibrary for RateLimit;

    /// @notice event emitted when buffer cap is updated
    event BufferCapUpdate(uint256 oldBufferCap, uint256 newBufferCap);

    /// @notice event emitted when rate limit per second is updated
    event RateLimitPerSecondUpdate(
        uint256 oldRateLimitPerSecond,
        uint256 newRateLimitPerSecond
    );

    /// @notice event emitted when buffer gets eaten into
    event BufferUsed(uint256 amountUsed, uint256 bufferRemaining);

    /// @notice event emitted when buffer gets replenished
    event BufferReplenished(uint256 amountReplenished, uint256 bufferRemaining);

    /// @notice rate limited v2 contract
    MockDynamicRateLimited rlm;

    /// @notice maximum rate limit per second in RateLimitedV2
    uint256 private constant maxRateLimitPerSecond = 1_000_000e18;

    /// @notice rate limit per second in RateLimitedV2
    uint256 private constant rateLimitPerSecond = 10e18;

    /// @notice buffer cap in RateLimitedV2
    uint128 private constant bufferCap = 10_000_000e18;

    /// @notice starting tvl in DynamicRateLimited
    uint256 private constant startingTvl = 100_000_000e18;

    function setUp() public {
        vm.warp(1);
        rlm = new MockDynamicRateLimited(
            uint128(rateLimitPerSecond),
            uint128(bufferCap),
            uint128(startingTvl)
        );
    }

    function testSetup() public {
        assertEq(rlm.startingTvl(), startingTvl);
        assertEq(rlm.bufferCap(), bufferCap);
        assertEq(rlm.rateLimitPerSecond(), rateLimitPerSecond);
        assertEq(rlm.buffer(), bufferCap); /// buffer has not been depleted
    }

    function testDepleteBuffer(uint128 amountToPull, uint16 warpAmount) public {
        if (amountToPull > rlm.bufferCap()) {
            vm.expectRevert("RateLimited: rate limit hit");
            rlm.depleteBuffer(amountToPull);
        } else {
            vm.expectEmit(true, false, false, true, address(rlm));
            emit BufferUsed(amountToPull, bufferCap - amountToPull);
            rlm.depleteBuffer(amountToPull);

            uint256 endingBuffer = rlm.buffer();
            assertEq(endingBuffer, bufferCap - amountToPull);
            assertEq(block.timestamp, rlm.lastBufferUsedTime());

            /// assert buffer cap and rate limit per second are scaled down based on new TVL
            assertEq(
                rlm.bufferCap(),
                (bufferCap * (startingTvl - amountToPull)) / startingTvl
            );
            assertEq(
                rlm.rateLimitPerSecond(),
                (rateLimitPerSecond * (startingTvl - amountToPull)) /
                    startingTvl
            );

            vm.warp(block.timestamp + warpAmount);

            uint256 accruedBuffer = warpAmount * rlm.rateLimitPerSecond();
            uint256 expectedBuffer = Math.min(
                endingBuffer + accruedBuffer,
                rlm.bufferCap()
            );
            assertEq(expectedBuffer, rlm.buffer());
        }
    }

    function testReplenishBuffer(
        uint128 amountToReplenish,
        uint16 warpAmount
    ) public {
        {
            uint256 amountToPull = rlm.buffer();
            uint256 startingBufferCap = rlm.bufferCap();
            uint256 startingRateLimitPerSecond = rlm.rateLimitPerSecond();
            uint256 currentTvl = rlm.startingTvl();

            rlm.depleteBuffer(amountToPull); /// fully exhaust buffer
            assertEq(rlm.buffer(), 0);

            /// assert buffer cap and rate limit per second are scaled down based on new TVL
            assertEq(
                rlm.bufferCap(),
                (startingBufferCap * (currentTvl - amountToPull)) / currentTvl
            );
            assertEq(
                rlm.rateLimitPerSecond(),
                (startingRateLimitPerSecond * (currentTvl - amountToPull)) /
                    currentTvl
            );
        }

        uint256 newBufferCap = rlm.bufferCap(); /// buffer cap has been updated with the draw down in rate limit
        uint256 actualAmountToReplenish = Math.min(
            amountToReplenish,
            newBufferCap
        );
        vm.expectEmit(true, false, false, true, address(rlm));
        emit BufferReplenished(amountToReplenish, actualAmountToReplenish);

        rlm.replenishBuffer(amountToReplenish);
        assertEq(rlm.buffer(), actualAmountToReplenish);
        assertEq(block.timestamp, rlm.lastBufferUsedTime());

        vm.warp(block.timestamp + warpAmount);

        uint256 newRateLimitPerSecond = rlm.rateLimitPerSecond();
        uint256 accruedBuffer = warpAmount * newRateLimitPerSecond;
        uint256 expectedBuffer = Math.min(
            amountToReplenish + accruedBuffer,
            rlm.buffer()
        );
        assertEq(expectedBuffer, rlm.buffer());
    }

    function testDepleteThenReplenishBuffer(
        uint128 amountToDeplete,
        uint128 amountToReplenish,
        uint16 warpAmount
    ) public {
        testDepleteBuffer(amountToDeplete, 0);
        testReplenishBuffer(amountToReplenish, 0);

        vm.warp(block.timestamp + warpAmount);

        uint256 accruedBuffer = warpAmount * rlm.rateLimitPerSecond();
        uint256 expectedBuffer = Math.min(
            rlm.bufferStored() + accruedBuffer,
            rlm.bufferCap()
        );
        assertEq(expectedBuffer, rlm.buffer());
    }

    function testReplenishWhenAtBufferCapHasNoEffect(
        uint128 amountToReplenish
    ) public {
        rlm.replenishBuffer(amountToReplenish);
        assertEq(rlm.buffer(), bufferCap);
        assertEq(block.timestamp, rlm.lastBufferUsedTime());
    }
}
