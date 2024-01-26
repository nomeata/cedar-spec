forbid(
  principal in rsss::a::"66",
  action in [rsss::Action::"action"],
  resource is rsss::a in rsss::a::""
) when {
  true && ((if (principal has "66z\u{12}666") then action else rsss::a::"66") has "")
};
