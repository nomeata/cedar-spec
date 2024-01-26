@r("66666\u{1}")
permit(
  principal,
  action == r::r::B::r::Action::"action",
  resource
) when {
  false
};
