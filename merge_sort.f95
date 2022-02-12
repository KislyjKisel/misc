module m
    implicit none
contains

    subroutine merge(arr, l, r, c)
        integer, dimension(:) :: arr
        integer, intent(in) :: l, r, c
        integer :: i, j, i1, j1, k, n
        
        integer, dimension(:), allocatable :: cpy
        
        n = r - l + 1
        k = 1
        
        allocate(cpy(n))
        
        i = l
        i1 = c
        
        j = c + 1
        j1 = r
        
        do k = 1, n
            if ( j > j1 .or. (i <= i1 .and. arr(i) <= arr(j)) ) then
            
                cpy(k) = arr(i)
                i = i + 1
            
            else
                
                cpy(k) = arr(j)
                j = j + 1
                
            end if
        end do
        
        do k = 1, n
            arr(l + k - 1) = cpy(k)
        end do
        
        deallocate(cpy)
        
    end subroutine merge
    
    recursive subroutine mergesort(arr, l, r)
        integer, dimension(:), intent(in) :: arr
        integer, intent(in) :: l, r
        integer :: c
        
        if (r > l) then
            c = l + (r - l) / 2
            call mergesort(arr, l, c)
            call mergesort(arr, c + 1, r)
            call merge(arr, l, r, c)
        end if

    end subroutine mergesort

    subroutine print1d(arr, i1, i2)
        integer, dimension(:), intent(in) :: arr
        integer, intent(in) :: i1, i2
        integer :: i
              
        print "(i1)", arr(i1:i2)
    
    end subroutine print1d

    subroutine print2d(arr, k, n)
        integer, dimension(:, :), intent(in) :: arr
        integer, intent(in) :: k, n
        integer :: i, j
        
        do i = 1, k
            print*, "Array#", i
            call print1d(arr(i, :), 1, n)
        end do
    
    end subroutine print2d
    
end module

program hello
    use m
    
    implicit none
    integer :: n, k
    integer, dimension (:, :), allocatable :: arr
    integer :: i, j
    
    read (*, *) k, n
    allocate(arr(k, n))
    
    do i = 1, k
        print*, "Array #", i
        do j = 1, n
            read*, arr(i, j)
        end do
        call print1d(arr(i,:), 1, n)
    end do
    print*, "End of input."
    
    do i = 1, k
        call mergesort(arr(i,:), 1, n)
    end do
    
    call print2d(arr, k, n)
    
    
    deallocate(arr)
    
end program Hello
