forbid(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  (true && (if (action * 32639) then false else resource)) && a::"jj\0\0\0\0\0\0\0\0\0j"
};
