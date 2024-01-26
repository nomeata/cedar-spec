@r("jjjjjjjj\0\0\0\0@jj\u{10}jj\0j")
permit(
  principal,
  action in [Action::""],
  resource == a::""
) when {
  (true && (!(![context, principal]))) && principal
};
