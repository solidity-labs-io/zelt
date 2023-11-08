pragma solidity =0.8.19;

import {RateLimitMidPoint, RateLimitMidpointCommonLibrary} from "@src/RateLimitMidpointCommonLibrary.sol";
import {RateLimitedMidpointLibrary} from "@src/RateLimitedMidpointLibrary.sol";
import {RateLimitedMidpoint} from "@src/RateLimitedMidpoint.sol";

contract MockRateLimitedMidpoint is RateLimitedMidpoint {
    using RateLimitMidpointCommonLibrary for RateLimitMidPoint;
    using RateLimitedMidpointLibrary for RateLimitMidPoint;

    constructor(
        uint256 _maxRateLimitPerSecond,
        uint128 _rateLimitPerSecond,
        uint112 _bufferCap
    )
        RateLimitedMidpoint(
            _maxRateLimitPerSecond,
            _rateLimitPerSecond,
            _bufferCap
        )
    {}

    function depleteBuffer(uint256 amount) public {
        _depleteBuffer(amount);
    }

    function replenishBuffer(uint256 amount) public {
        _replenishBuffer(amount);
    }

    function setRateLimitPerSecond(uint128 newRateLimitPerSecond) public {
        _setRateLimitPerSecond(newRateLimitPerSecond);
    }

    function setBufferCap(uint112 newBufferCap) public {
        _setBufferCap(newBufferCap);
    }

    function sync() public {
        rateLimit.sync();
    }

    function bufferCap() public view returns (uint256) {
        return rateLimit.bufferCap;
    }

    function midPoint() public view returns (uint256) {
        return rateLimit.midPoint;
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
