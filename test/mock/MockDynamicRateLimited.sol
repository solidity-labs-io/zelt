pragma solidity =0.8.19;

import {SafeCast} from "@openzeppelin/contracts/utils/math/SafeCast.sol";

import {RateLimited} from "@src/RateLimited.sol";
import {RateLimitCommonLibrary} from "@src/RateLimitCommonLibrary.sol";
import {DynamicRateLimitLibrary, RateLimit} from "@src/DynamicRateLimitLibrary.sol";

contract MockDynamicRateLimited {
    using DynamicRateLimitLibrary for RateLimit;
    using RateLimitCommonLibrary for RateLimit;

    RateLimit public rateLimit;

    uint256 public startingTvl;

    constructor(
        uint128 _rateLimitPerSecond,
        uint128 _bufferCap,
        uint128 _startingTvl
    ) {
        rateLimit.lastBufferUsedTime = uint32(block.timestamp); /// only access struct directly to prevent overflow on buffer calc in setBufferCap
        rateLimit.setBufferCap(_bufferCap);
        rateLimit.bufferStored = _bufferCap; /// manually set this as first call to setBufferCap sets it to 0
        rateLimit.setRateLimitPerSecond(_rateLimitPerSecond);

        startingTvl = _startingTvl;
    }

    function depleteBuffer(uint256 amount) public {
        rateLimit.depleteBuffer(amount, startingTvl);
        startingTvl -= amount;
    }

    function replenishBuffer(uint256 amount) public {
        rateLimit.replenishBuffer(amount, startingTvl);
        startingTvl += amount;
    }

    function bufferCap() public view returns (uint256) {
        return rateLimit.bufferCap;
    }

    function buffer() public view returns (uint256) {
        return rateLimit.buffer();
    }

    function rateLimitPerSecond() public view returns (uint256) {
        return rateLimit.rateLimitPerSecond;
    }

    function lastBufferUsedTime() public view returns (uint256) {
        return rateLimit.lastBufferUsedTime;
    }

    function bufferStored() public view returns (uint256) {
        return rateLimit.bufferStored;
    }
}
