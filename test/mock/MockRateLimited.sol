pragma solidity =0.8.19;

import {RateLimited} from "@src/impl/RateLimited.sol";

contract MockRateLimited is RateLimited {
    constructor(
        uint256 _maxRateLimitPerSecond,
        uint128 _rateLimitPerSecond,
        uint128 _bufferCap
    )
        RateLimited(_maxRateLimitPerSecond, _rateLimitPerSecond, _bufferCap)
    {}

    function depleteBuffer(uint256 amount) public {
        _depleteBuffer(amount);
    }

    function replenishBuffer(uint256 amount) public {
        _replenishBuffer(amount);
    }

    function bufferCap() public view returns (uint256) {
        return rateLimit.bufferCap;
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
