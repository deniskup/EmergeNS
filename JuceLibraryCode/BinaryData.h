/* =========================================================================================

   This is an auto-generated file: Any edits you make may be overwritten!

*/

#pragma once

namespace BinaryData
{
    extern const char*   Cholesky;
    const int            CholeskySize = 1206;

    extern const char*   CholmodSupport;
    const int            CholmodSupportSize = 1948;

    extern const char*   Core;
    const int            CoreSize = 13183;

    extern const char*   Dense;
    const int            DenseSize = 129;

    extern const char*   Eigen;
    const int            EigenSize = 37;

    extern const char*   Eigenvalues;
    const int            EigenvaluesSize = 1837;

    extern const char*   Geometry;
    const int            GeometrySize = 1999;

    extern const char*   Householder;
    const int            HouseholderSize = 858;

    extern const char*   IterativeLinearSolvers;
    const int            IterativeLinearSolversSize = 2131;

    extern const char*   Jacobi;
    const int            JacobiSize = 926;

    extern const char*   KLUSupport;
    const int            KLUSupportSize = 1430;

    extern const char*   LU;
    const int            LUSize = 1315;

    extern const char*   MetisSupport;
    const int            MetisSupportSize = 1026;

    extern const char*   OrderingMethods;
    const int            OrderingMethodsSize = 2521;

    extern const char*   PardisoSupport;
    const int            PardisoSupportSize = 1151;

    extern const char*   PaStiXSupport;
    const int            PaStiXSupportSize = 1800;

    extern const char*   QR;
    const int            QRSize = 1322;

    extern const char*   QtAlignedMalloc;
    const int            QtAlignedMallocSize = 939;

    extern const char*   Sparse;
    const int            SparseSize = 922;

    extern const char*   SparseCholesky;
    const int            SparseCholeskySize = 1272;

    extern const char*   SparseCore;
    const int            SparseCoreSize = 2309;

    extern const char*   SparseLU;
    const int            SparseLUSize = 1864;

    extern const char*   SparseQR;
    const int            SparseQRSize = 1231;

    extern const char*   SPQRSupport;
    const int            SPQRSupportSize = 1196;

    extern const char*   StdDeque;
    const int            StdDequeSize = 824;

    extern const char*   StdList;
    const int            StdListSize = 752;

    extern const char*   StdVector;
    const int            StdVectorSize = 830;

    extern const char*   SuperLUSupport;
    const int            SuperLUSupportSize = 2307;

    extern const char*   SVD;
    const int            SVDSize = 1634;

    extern const char*   UmfPackSupport;
    const int            UmfPackSupportSize = 1422;

    extern const char*   default_nslayout;
    const int            default_nslayoutSize = 2547;

    // Number of elements in the namedResourceList and originalFileNames arrays.
    const int namedResourceListSize = 31;

    // Points to the start of a list of resource names.
    extern const char* namedResourceList[];

    // Points to the start of a list of resource filenames.
    extern const char* originalFilenames[];

    // If you provide the name of one of the binary resource variables above, this function will
    // return the corresponding data and its size (or a null pointer if the name isn't found).
    const char* getNamedResource (const char* resourceNameUTF8, int& dataSizeInBytes);

    // If you provide the name of one of the binary resource variables above, this function will
    // return the corresponding original, non-mangled filename (or a null pointer if the name isn't found).
    const char* getNamedResourceOriginalFilename (const char* resourceNameUTF8);
}
